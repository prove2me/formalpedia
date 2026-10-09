-- Prove2me | solution 1 for OAI.Erdos3.replacementCommonInputLog_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T19:14:07.720086+00:00
-- url     : https://prove2.me/submissions/460b09eb-e9e7-46bd-8b95-e70dbcb61c61

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmallWeightedPhysicalReplacement
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem physicalReplacementInputLog_nonneg (m n : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ physicalReplacementInputLog m n P := by
  unfold physicalReplacementInputLog
  positivity

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

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.InitialBudgetJointReplacement
namespace OAI

section

namespace Erdos3

theorem replacementCutoffInputLog_bounds (m n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ replacementCutoffInputLog m n d P ∧
    P ≤ replacementCutoffInputLog m n d P ∧
    6 * physicalReplacementInputLog m n P + 6 ≤ replacementCutoffInputLog m n d P ∧
    3 * (d : ℝ) + 2 ≤ replacementCutoffInputLog m n d P ∧
    2 * (d : ℝ) ≤ replacementCutoffInputLog m n d P := by
  have hW := physicalReplacementInputLog_nonneg m n hP
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  unfold replacementCutoffInputLog
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem replacementCommonInputLog_bounds (m n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ replacementCommonInputLog m n d P ∧
    P ≤ replacementCommonInputLog m n d P ∧
    replacementCutoffInputLog m n d P ≤ replacementCommonInputLog m n d P ∧
    4 * replacementCutoffInputLog m n d P + 6 ≤ replacementCommonInputLog m n d P ∧
    3 * replacementCutoffInputLog m n d P + 6 ≤ replacementCommonInputLog m n d P ∧
    2 * P + 3 ≤ replacementCommonInputLog m n d P := by
  have hb := replacementCutoffInputLog_bounds m n d hP
  unfold replacementCommonInputLog
  constructor
  · linarith [hb.1]
  constructor
  · linarith [hb.1]
  constructor
  · linarith [hb.1]
  constructor
  · linarith
  constructor <;> linarith [hb.1]

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

open scoped BigOperators Classical

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.replacementCommonInputLog_bounds := @OAI.Erdos3.replacementCommonInputLog_bounds
