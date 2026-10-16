-- Prove2me | solution 1 for OAI.Erdos3.unconditionedCommonSideScalarRatio_two_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T03:30:05.140988+00:00
-- url     : https://prove2.me/submissions/9ce26c7b-2c13-4fa6-8e78-fbd2a70dde22

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1328

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.UnconditionedScalarScaleNiltestBase
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical NNReal TensorProduct
namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical NNReal TensorProduct
namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical NNReal TensorProduct

theorem unconditionedScalarPrimeRatio_two_le (n : ℕ) :
    2 ≤ unconditionedScalarPrimeRatio n := by
  unfold unconditionedScalarPrimeRatio
  omega

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnconditionedCommonSideScalarRatioBounds
namespace OAI

section

namespace Erdos3

theorem unconditionedCommonSideScalarRatio_two_le_oai {n : ℕ} (hn : 1 ≤ n) :
    2 ≤ unconditionedCommonSideScalarRatio n := by
  have hmul := Nat.mul_le_mul hn (unconditionedScalarPrimeRatio_two_le n)
  unfold unconditionedCommonSideScalarRatio
  omega

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.unconditionedCommonSideScalarRatio_two_le_oai := @OAI.Erdos3.unconditionedCommonSideScalarRatio_two_le_oai
