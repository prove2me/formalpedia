-- Prove2me | solution 1 for OAI.Erdos3.scalarInitialReferenceInput_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-13T05:07:20.568986+00:00
-- url     : https://prove2.me/submissions/b95317f9-9d76-4ff6-adb6-a9e6a96a955f

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B165
import Theorems.Thm_OAI_Erdos3_physicalPairCoefficientLog_bounds
import Theorems.Thm_OAI_Erdos3_replacementCommonInputLog_bounds

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndexedComparableScalarGeometryData
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem scalarInitialReferenceInput_bounds (m n d : ℕ) {p P0 : ℝ} (hp : 0 ≤ p) (hP0 : 0 ≤ P0) :
    let Z := replacementCommonInputLog m n d P0
    let G := 2 * physicalPairCoefficientLog n d Z + 2
    let U := scalarInitialReferenceInput m n d p P0
    0 ≤ U ∧ Z ≤ U ∧ G + P0 + 2 ≤ U ∧ P0 ≤ U ∧
      (m : ℝ) ≤ U ∧ (n : ℝ) ≤ U ∧ (d : ℝ) ≤ U ∧ scalarTransferTail (3 * p) ≤ U ∧ p ≤ U := by
  intro Z G U
  have hZ : 0 ≤ Z := (replacementCommonInputLog_bounds m n d hP0).1
  have hG : 0 ≤ G := by
    have h := (physicalPairCoefficientLog_bounds n d hZ).1
    dsimp only [G]
    linarith
  have hT : 0 ≤ scalarTransferTail (3 * p) := by unfold scalarTransferTail; positivity
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  dsimp only [U, scalarInitialReferenceInput]
  dsimp only [G, Z] at hG hZ ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.scalarInitialReferenceInput_bounds := @OAI.Erdos3.scalarInitialReferenceInput_bounds
