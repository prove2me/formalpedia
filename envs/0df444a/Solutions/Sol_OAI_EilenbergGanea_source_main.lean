-- Prove2me | solution 1 for OAI.EilenbergGanea.source_main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T06:55:17.553993+00:00
-- url     : https://prove2.me/submissions/810d821c-8764-4100-a2a1-c1b6c4c9ade2

import Mathlib
import Definitions.Def_EilenbergGanea
import Definitions.Def_OAIEGC004
import Theorems.Thm_OAI_EilenbergGanea_source_cohomologicalDimension
import Theorems.Thm_OAI_EilenbergGanea_source_finitely_generated
import Theorems.Thm_OAI_EilenbergGanea_source_hasClassifyingSpace_three
import Theorems.Thm_OAI_EilenbergGanea_source_no_classifyingSpace_two
import Theorems.Thm_OAI_EilenbergGanea_source_residuallyFinite

section
-- module Solutions.OAIEG.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Metric Topology

namespace EilenbergGanea
universe u

/-- Source Theorem1.1 for the exact103-cell flag triangulation and its actual
Artin height kernel. The last conjunct is polymorphic in the universe of the
hypothetical ordinary CW model, with unrestricted numbers of cells. -/
theorem source_main_oai :
    Group.FG SourceGroup ∧ Group.ResiduallyFinite SourceGroup ∧
    cohomologicalDimension SourceGroup = 2 ∧
    HasClassifyingSpace.{0} SourceGroup 3 ∧
    ¬ HasClassifyingSpace.{u} SourceGroup 2 :=
  ⟨source_finitely_generated,source_residuallyFinite,source_cohomologicalDimension,
    source_hasClassifyingSpace_three,source_no_classifyingSpace_two⟩

end EilenbergGanea


end

end OAI
end

theorem solution.{u} : type_of% @OAI.EilenbergGanea.source_main_oai.{u} := @OAI.EilenbergGanea.source_main_oai.{u}
