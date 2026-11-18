-- Prove2me | solution 1 for OAI.EditApproximation.computedQueryAnswerWithWork_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:34:06.274231+00:00
-- url     : https://prove2.me/submissions/dff25499-6724-48f8-bf20-e46d370600b9

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea002
import Theorems.Thm_OAI_EditApproximation_computedQueryMemoResult_decode

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryFinalAnswer
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Clamp the final value to the input length and round down by binary division. -/


theorem finalAnswerWithWork_value (N : ℕ) (a : BinaryFraction) :
    bitWordValue (finalAnswerWithWork N a).1 = integerAnswer N (a.value : ℝ) := by
  have hfloor : ⌊(a.value : ℝ)⌋₊ = ⌊a.value⌋₊ := by
    apply Nat.floor_congr
    intro n
    norm_cast
  simp only [finalAnswerWithWork, wordMinWithWork_value, bitWordValue_bits, naturalFloorWithWork_value]
  rw [← hfloor]
  unfold integerAnswer
  by_cases hn : a.value ≤ 0
  · have hnR : (a.value : ℝ) ≤ 0 := by exact_mod_cast hn
    rw [Nat.floor_of_nonpos hnR, min_eq_right (Nat.zero_le N)]
    have hm : min (N : ℝ) (a.value : ℝ) ≤ 0 := (min_le_right _ _).trans hnR
    rw [max_eq_left hm, Nat.floor_zero]
  · have hnR : 0 ≤ (a.value : ℝ) := by exact_mod_cast (le_of_not_ge hn)
    have hm : 0 ≤ min (N : ℝ) (a.value : ℝ) := le_min (Nat.cast_nonneg _) hnR
    rw [max_eq_right hm]
    by_cases hN : (a.value : ℝ) ≤ N
    · have hf : ⌊(a.value : ℝ)⌋₊ ≤ N := by
        simpa only [Nat.floor_natCast] using Nat.floor_mono hN
      rw [min_eq_right hN, min_eq_right hf]
    · have hf : N ≤ ⌊(a.value : ℝ)⌋₊ := Nat.le_floor (le_of_not_ge hN)
      rw [min_eq_left (le_of_not_ge hN), Nat.floor_natCast, min_eq_left hf]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryAnswer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
attribute [local instance] queryArityNeZero queryRoundsNeZero

theorem computedQueryAnswerWithWork_value_oai (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) (hf : 3 ≤ smallLogExponent N)
    (hsize : source.length + target.length ≤ N)
    (hMass : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx) :
    bitWordValue (computedQueryAnswerWithWork source target N occurrence symbolBits positionBits input).1 =
      if source = target then 0 else integerAnswer N ((computedFamilyResult source target N input).value : ℝ) := by
  have h := congrArg RecursiveMemoResult.value (computedQueryMemoResult_decode source target N occurrence
    symbolBits positionBits input hN hell hf hsize hMass hs ht hp htable)
  change (computedQueryMemoResult source target N occurrence symbolBits positionBits input).value.value =
    (computedFamilyResult source target N input).value at h
  unfold computedQueryAnswerWithWork
  split_ifs
  · rfl
  · dsimp only
    rw [BinaryFraction.finalAnswerWithWork_value, h]

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.computedQueryAnswerWithWork_value_oai := @OAI.EditApproximation.computedQueryAnswerWithWork_value_oai
