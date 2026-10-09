-- Prove2me | solution 1 for OAI.Erdos3.physicalPairCoefficientLog_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T17:31:15.993054+00:00
-- url     : https://prove2.me/submissions/5d117b48-e715-4dc6-b3c6-0e8be8489526

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothPairErrorLogBounds
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem smoothPairRowErrorLog_nonneg (d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ smoothPairRowErrorLog d P := by
  unfold smoothPairRowErrorLog
  positivity

theorem smoothPairErrorLog_nonneg (n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ smoothPairErrorLog n d P := by
  have hr := smoothPairRowErrorLog_nonneg d hP
  unfold smoothPairErrorLog
  positivity

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalPairAccuracyLogBounds
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

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

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem physicalPairCoefficientLog_bounds (n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ physicalPairCoefficientLog n d P ∧
    P ≤ physicalPairCoefficientLog n d P ∧
    6 + 2 * n * P + 2 * n + smoothPairErrorLog n d P ≤ physicalPairCoefficientLog n d P ∧
    2 + 4 * (2 + d) + P ≤ physicalPairCoefficientLog n d P ∧
    20 + 2 * n * P + 2 * n + n * (5 * P + 11) + 9 * P ≤ physicalPairCoefficientLog n d P := by
  have hF := smoothPairErrorLog_nonneg n d hP
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hnp := mul_nonneg hn hP
  unfold physicalPairCoefficientLog
  constructor
  · positivity
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.physicalPairCoefficientLog_bounds := @OAI.Erdos3.physicalPairCoefficientLog_bounds
