-- Prove2me | solution 1 for OAI.Erdos3.smoothPairCoefficientScale_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T11:27:00.727654+00:00
-- url     : https://prove2.me/submissions/75672a75-e490-4939-a307-558355d4e391

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

theorem smoothPairCoefficientScale_pos {J : Type*} {H L : ℝ} (hH : 0 < H) (hL : 0 < L) :
    ∀ c : Option J, 0 < smoothPairCoefficientScale H L c := by
  intro c
  cases c
  · exact hH
  · exact div_pos hH hL

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

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.smoothPairCoefficientScale_pos.{u_1} := @OAI.Erdos3.smoothPairCoefficientScale_pos.{u_1}
