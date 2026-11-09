-- Prove2me | solution 1 for OAI.SharpPlanar.normalizedH_table_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T08:43:24.807409+00:00
-- url     : https://prove2.me/submissions/34deb127-8a54-4d4d-b6e7-158e61bb0468

import Mathlib
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1695
import Theorems.Thm_OAI_SharpPlanar_fullMoment_direct_g
import Theorems.Thm_OAI_SharpPlanar_tableMomentK_eq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FullMomentBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped BigOperators
lemma fullMoment_transformed (a : Bool) (m : ℝ) (ell : ℕ) :
    fullMoment a true m ell=K (tableData a) ell m/(ell.factorial:ℝ) :=
  tableMomentK_eq_g a m ell
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CoarseTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma normalizedH_table_g_oai (a : Bool) (m : ℝ) (ell : ℕ) :
    normalizedH a m ell=tableHJet a ell m/(ell.factorial:ℝ) := by
  simp only [normalizedH,fullMoment_direct_g,fullMoment_transformed,tableHJet,add_div]
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.normalizedH_table_g_oai := @OAI.SharpPlanar.normalizedH_table_g_oai
