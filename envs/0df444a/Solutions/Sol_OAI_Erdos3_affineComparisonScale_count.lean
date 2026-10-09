-- Prove2me | solution 1 for OAI.Erdos3.affineComparisonScale_count
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T18:13:40.306067+00:00
-- url     : https://prove2.me/submissions/6ca26855-757d-4820-9b6f-347762e826c1

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B090
import Theorems.Thm_OAI_Erdos3_affineComparisonScale_bounds

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffinePrimitiveLogBudget
namespace OAI

section

namespace Erdos3

theorem affineComparisonScale_count {ι : Type*} [Fintype ι] {ε L T C : ℝ}
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C) :
    (Fintype.card ι : ℝ) ≤ Real.exp (affineComparisonScale ε L T C) :=
  hcount.trans (Real.exp_le_exp.mpr (affineComparisonScale_bounds (ε := ε) hL hT hC).2.2.2)

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

end OAI

end

theorem solution.{u_1} : type_of% @OAI.Erdos3.affineComparisonScale_count.{u_1} := @OAI.Erdos3.affineComparisonScale_count.{u_1}
