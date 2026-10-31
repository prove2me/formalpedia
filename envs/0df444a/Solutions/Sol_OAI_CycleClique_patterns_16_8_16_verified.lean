-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_16_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:39:22.136113+00:00
-- url     : https://prove2.me/submissions/69c341c9-8db2-46bb-b799-a7c6e4c6c8ae

import Mathlib
import Definitions.Def_OAIQ107D130
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates063
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2008_checked : certificate_2008.Valid 16 8 16 certificate_2008_q certificate_2008_edges 8 5 [] := by decide +kernel
theorem certificate_2008_valid : certificate_2008.Valid 16 8 (patternOrder [[],[],[2,1,2,1,2]]) (patternClique [[],[],[2,1,2,1,2]]) (patternEdges [[],[],[2,1,2,1,2]]) (patternAmount [[],[],[2,1,2,1,2]]) (patternEdgeCount [[],[],[2,1,2,1,2]]) [] := certificate_2008_checked

theorem certificate_2009_checked : certificate_2009.Valid 16 8 16 certificate_2009_q certificate_2009_edges 8 4 [] := by decide +kernel
theorem certificate_2009_valid : certificate_2009.Valid 16 8 (patternOrder [[],[],[2,2],[2,2]]) (patternClique [[],[],[2,2],[2,2]]) (patternEdges [[],[],[2,2],[2,2]]) (patternAmount [[],[],[2,2],[2,2]]) (patternEdgeCount [[],[],[2,2],[2,2]]) [] := certificate_2009_checked

theorem certificate_2010_checked : certificate_2010.Valid 16 8 12 certificate_2010_q certificate_2010_edges 4 4 [] := by decide +kernel
theorem certificate_2010_valid : certificate_2010.Valid 16 8 (patternOrder [[],[1],[1],[1,1]]) (patternClique [[],[1],[1],[1,1]]) (patternEdges [[],[1],[1],[1,1]]) (patternAmount [[],[1],[1],[1,1]]) (patternEdgeCount [[],[1],[1],[1,1]]) [] := certificate_2010_checked

theorem certificate_2011_checked : certificate_2011.Valid 16 8 13 certificate_2011_q certificate_2011_edges 5 4 [] := by decide +kernel
theorem certificate_2011_valid : certificate_2011.Valid 16 8 (patternOrder [[],[1],[1],[1,2]]) (patternClique [[],[1],[1],[1,2]]) (patternEdges [[],[1],[1],[1,2]]) (patternAmount [[],[1],[1],[1,2]]) (patternEdgeCount [[],[1],[1],[1,2]]) [] := certificate_2011_checked

theorem certificate_2012_checked : certificate_2012.Valid 16 8 14 certificate_2012_q certificate_2012_edges 6 4 [] := by decide +kernel
theorem certificate_2012_valid : certificate_2012.Valid 16 8 (patternOrder [[],[1],[1],[1,3]]) (patternClique [[],[1],[1],[1,3]]) (patternEdges [[],[1],[1],[1,3]]) (patternAmount [[],[1],[1],[1,3]]) (patternEdgeCount [[],[1],[1],[1,3]]) [] := certificate_2012_checked

theorem certificate_2013_checked : certificate_2013.Valid 16 8 15 certificate_2013_q certificate_2013_edges 7 4 [] := by decide +kernel
theorem certificate_2013_valid : certificate_2013.Valid 16 8 (patternOrder [[],[1],[1],[1,4]]) (patternClique [[],[1],[1],[1,4]]) (patternEdges [[],[1],[1],[1,4]]) (patternAmount [[],[1],[1],[1,4]]) (patternEdgeCount [[],[1],[1],[1,4]]) [] := certificate_2013_checked

theorem certificate_2014_checked : certificate_2014.Valid 16 8 16 certificate_2014_q certificate_2014_edges 8 4 [] := by decide +kernel
theorem certificate_2014_valid : certificate_2014.Valid 16 8 (patternOrder [[],[1],[1],[1,5]]) (patternClique [[],[1],[1],[1,5]]) (patternEdges [[],[1],[1],[1,5]]) (patternAmount [[],[1],[1],[1,5]]) (patternEdgeCount [[],[1],[1],[1,5]]) [] := certificate_2014_checked

theorem certificate_2015_checked : certificate_2015.Valid 16 8 14 certificate_2015_q certificate_2015_edges 6 4 [] := by decide +kernel
theorem certificate_2015_valid : certificate_2015.Valid 16 8 (patternOrder [[],[1],[1],[2,2]]) (patternClique [[],[1],[1],[2,2]]) (patternEdges [[],[1],[1],[2,2]]) (patternAmount [[],[1],[1],[2,2]]) (patternEdgeCount [[],[1],[1],[2,2]]) [] := certificate_2015_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates064
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2016_checked : certificate_2016.Valid 16 8 15 certificate_2016_q certificate_2016_edges 7 4 [] := by decide +kernel
theorem certificate_2016_valid : certificate_2016.Valid 16 8 (patternOrder [[],[1],[1],[2,3]]) (patternClique [[],[1],[1],[2,3]]) (patternEdges [[],[1],[1],[2,3]]) (patternAmount [[],[1],[1],[2,3]]) (patternEdgeCount [[],[1],[1],[2,3]]) [] := certificate_2016_checked

theorem certificate_2017_checked : certificate_2017.Valid 16 8 16 certificate_2017_q certificate_2017_edges 8 4 [] := by decide +kernel
theorem certificate_2017_valid : certificate_2017.Valid 16 8 (patternOrder [[],[1],[1],[2,4]]) (patternClique [[],[1],[1],[2,4]]) (patternEdges [[],[1],[1],[2,4]]) (patternAmount [[],[1],[1],[2,4]]) (patternEdgeCount [[],[1],[1],[2,4]]) [] := certificate_2017_checked

theorem certificate_2018_checked : certificate_2018.Valid 16 8 16 certificate_2018_q certificate_2018_edges 8 4 [] := by decide +kernel
theorem certificate_2018_valid : certificate_2018.Valid 16 8 (patternOrder [[],[1],[1],[3,3]]) (patternClique [[],[1],[1],[3,3]]) (patternEdges [[],[1],[1],[3,3]]) (patternAmount [[],[1],[1],[3,3]]) (patternEdgeCount [[],[1],[1],[3,3]]) [] := certificate_2018_checked

theorem certificate_2019_checked : certificate_2019.Valid 16 8 13 certificate_2019_q certificate_2019_edges 5 4 [] := by decide +kernel
theorem certificate_2019_valid : certificate_2019.Valid 16 8 (patternOrder [[],[1],[1,1],[2]]) (patternClique [[],[1],[1,1],[2]]) (patternEdges [[],[1],[1,1],[2]]) (patternAmount [[],[1],[1,1],[2]]) (patternEdgeCount [[],[1],[1,1],[2]]) [] := certificate_2019_checked

theorem certificate_2020_checked : certificate_2020.Valid 16 8 14 certificate_2020_q certificate_2020_edges 6 4 [] := by decide +kernel
theorem certificate_2020_valid : certificate_2020.Valid 16 8 (patternOrder [[],[1],[1,1],[3]]) (patternClique [[],[1],[1,1],[3]]) (patternEdges [[],[1],[1,1],[3]]) (patternAmount [[],[1],[1,1],[3]]) (patternEdgeCount [[],[1],[1,1],[3]]) [] := certificate_2020_checked

theorem certificate_2021_checked : certificate_2021.Valid 16 8 15 certificate_2021_q certificate_2021_edges 7 4 [] := by decide +kernel
theorem certificate_2021_valid : certificate_2021.Valid 16 8 (patternOrder [[],[1],[1,1],[4]]) (patternClique [[],[1],[1,1],[4]]) (patternEdges [[],[1],[1,1],[4]]) (patternAmount [[],[1],[1,1],[4]]) (patternEdgeCount [[],[1],[1,1],[4]]) [] := certificate_2021_checked

theorem certificate_2022_checked : certificate_2022.Valid 16 8 16 certificate_2022_q certificate_2022_edges 8 4 [] := by decide +kernel
theorem certificate_2022_valid : certificate_2022.Valid 16 8 (patternOrder [[],[1],[1,1],[5]]) (patternClique [[],[1],[1,1],[5]]) (patternEdges [[],[1],[1,1],[5]]) (patternAmount [[],[1],[1,1],[5]]) (patternEdgeCount [[],[1],[1,1],[5]]) [] := certificate_2022_checked

theorem certificate_2023_checked : certificate_2023.Valid 16 8 13 certificate_2023_q certificate_2023_edges 5 5 [] := by decide +kernel
theorem certificate_2023_valid : certificate_2023.Valid 16 8 (patternOrder [[],[1],[1,1,1,1]]) (patternClique [[],[1],[1,1,1,1]]) (patternEdges [[],[1],[1,1,1,1]]) (patternAmount [[],[1],[1,1,1,1]]) (patternEdgeCount [[],[1],[1,1,1,1]]) [] := certificate_2023_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns16x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_16_8_16_verified_oai : ∀ D ∈ patterns_16_8_16, PatternVerified 16 8 D := by

  simp only [patterns_16_8_16, List.forall_mem_cons]

  exact ⟨⟨certificate_2008, certificate_2008_valid⟩, ⟨⟨certificate_2009, certificate_2009_valid⟩, ⟨⟨certificate_2010, certificate_2010_valid⟩, ⟨⟨certificate_2011, certificate_2011_valid⟩, ⟨⟨certificate_2012, certificate_2012_valid⟩, ⟨⟨certificate_2013, certificate_2013_valid⟩, ⟨⟨certificate_2014, certificate_2014_valid⟩, ⟨⟨certificate_2015, certificate_2015_valid⟩, ⟨⟨certificate_2016, certificate_2016_valid⟩, ⟨⟨certificate_2017, certificate_2017_valid⟩, ⟨⟨certificate_2018, certificate_2018_valid⟩, ⟨⟨certificate_2019, certificate_2019_valid⟩, ⟨⟨certificate_2020, certificate_2020_valid⟩, ⟨⟨certificate_2021, certificate_2021_valid⟩, ⟨⟨certificate_2022, certificate_2022_valid⟩, ⟨⟨certificate_2023, certificate_2023_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_16_verified_oai := @OAI.CycleClique.patterns_16_8_16_verified_oai
