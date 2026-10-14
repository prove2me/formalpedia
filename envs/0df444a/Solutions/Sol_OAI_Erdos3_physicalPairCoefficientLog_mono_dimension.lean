-- Prove2me | solution 1 for OAI.Erdos3.physicalPairCoefficientLog_mono_dimension
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-13T04:59:30.582016+00:00
-- url     : https://prove2.me/submissions/97eaca0e-9064-448f-be66-b78818bece3b

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B165

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndexedComparableScalarGeometryData
namespace OAI

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem physicalPairCoefficientLog_mono_dimension (n : ℕ) {d e : ℕ} {P : ℝ}
    (hde : d ≤ e) (hP : 0 ≤ P) : physicalPairCoefficientLog n d P ≤ physicalPairCoefficientLog n e P := by
  have hde' : (d : ℝ) ≤ e := by exact_mod_cast hde
  unfold physicalPairCoefficientLog smoothPairErrorLog smoothPairRowErrorLog
  gcongr

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

theorem solution : type_of% @OAI.Erdos3.physicalPairCoefficientLog_mono_dimension := @OAI.Erdos3.physicalPairCoefficientLog_mono_dimension
