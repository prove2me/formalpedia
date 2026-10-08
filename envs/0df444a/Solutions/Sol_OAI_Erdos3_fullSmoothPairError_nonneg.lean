-- Prove2me | solution 1 for OAI.Erdos3.fullSmoothPairError_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:37:59.825909+00:00
-- url     : https://prove2.me/submissions/156c86d3-0f40-4aa3-b805-0c61359a4ca5

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B014

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AnisotropicSmoothPairLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix NNReal

theorem smoothPairProbabilityError_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (Q : ℕ) (C κ δ : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ smoothPairProbabilityError k Q C κ δ := by
  unfold smoothPairProbabilityError normalizedFiberErrorConstant integerFiberErrorConstant
  positivity

end Erdos3

end

end OAI

end

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

theorem fullSmoothPairError_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ δ : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ fullSmoothPairError n k Q C κ δ := by
  have he := smoothPairProbabilityError_nonneg k Q C κ δ hδ
  have hc : 0 ≤ smoothPairProbabilityCap k Q C κ := by
    unfold smoothPairProbabilityCap
    positivity
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) he)
    (pow_nonneg (add_nonneg hc he) _)

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

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.fullSmoothPairError_nonneg.{u_1} := @OAI.Erdos3.fullSmoothPairError_nonneg.{u_1}
