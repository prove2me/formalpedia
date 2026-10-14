-- Prove2me | solution 1 for OAI.Erdos3.scalarTransferAllocatedLogs_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-13T05:14:40.914604+00:00
-- url     : https://prove2.me/submissions/4d11e050-4e35-4d11-ac89-f1b631c9794c

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B165

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndexedComparableScalarGeometryData
namespace OAI

section

namespace Erdos3

theorem scalarTransferAllocatedLogs_bounds (b : ℕ) {common p Z U : ℝ}
    (hcommon : 0 ≤ common) (hp : 0 ≤ p) (hZ : 0 ≤ Z) (hU : 0 ≤ U) :
    0 ≤ scalarTransferCapLog b Z ∧ 0 ≤ scalarTransferAccuracyLog b p Z ∧
    0 ≤ scalarTransferCellLog common b p Z U ∧
    65536 * (common + 3) ^ 4 ≤ scalarTransferCellLog common b p Z U ∧
    Z * b + scalarTransferAccuracyLog b p Z + U + 1 ≤ scalarTransferCellLog common b p Z U ∧
    Z * b + U + 1 ≤ scalarTransferCellLog common b p Z U := by
  have hc : 0 ≤ scalarTransferCapLog b Z := by unfold scalarTransferCapLog; positivity
  have ha : 0 ≤ scalarTransferAccuracyLog b p Z := by unfold scalarTransferAccuracyLog; positivity
  have hside : 0 ≤ 65536 * (common + 3) ^ 4 := by positivity
  have hb : 0 ≤ Z * (b : ℝ) := mul_nonneg hZ (Nat.cast_nonneg b)
  unfold scalarTransferCellLog
  exact ⟨hc, ha, by positivity, by linarith, by linarith, by linarith⟩

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

theorem solution : type_of% @OAI.Erdos3.scalarTransferAllocatedLogs_bounds := @OAI.Erdos3.scalarTransferAllocatedLogs_bounds
