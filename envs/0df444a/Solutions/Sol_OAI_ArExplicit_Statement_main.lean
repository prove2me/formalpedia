-- Prove2me | solution 1 for OAI.ArExplicit.Statement.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T17:45:00.374282+00:00
-- url     : https://prove2.me/submissions/472f94fa-0c69-47d9-90d1-24039026ebaf

import Mathlib
import Definitions.Def_AuslanderReiten
import Definitions.Def_OAIQ031A191
import Theorems.Thm_OAI_ArExplicit_Statement_fullStatement_of_mainConclusions

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit
universe v

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

theorem counterexample_mainConclusions :
    MainConclusions BaseField counterexample.R counterexample.M :=
  verifiedCounterexample.property

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_All
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.Statement
universe v

theorem main_oai : FullStatement.{v} :=
  fullStatement_of_mainConclusions ArExplicit.counterexample
    ArExplicit.counterexample_mainConclusions

end ArExplicit.Statement

end OAI
end

theorem solution.{v} : type_of% @OAI.ArExplicit.Statement.main_oai.{v} := @OAI.ArExplicit.Statement.main_oai.{v}
