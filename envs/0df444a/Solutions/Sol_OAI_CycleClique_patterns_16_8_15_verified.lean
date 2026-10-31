-- Prove2me | solution 1 for OAI.CycleClique.patterns_16_8_15_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:31:40.918019+00:00
-- url     : https://prove2.me/submissions/50b48b88-c865-4a7a-960c-0efdc50f3a01

import Mathlib
import Definitions.Def_OAIQ107D003
import Definitions.Def_OAIQ107D062
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

theorem certificate_1992_checked : certificate_1992.Valid 16 8 15 certificate_1992_q certificate_1992_edges 7 4 [] := by decide +kernel
theorem certificate_1992_valid : certificate_1992.Valid 16 8 (patternOrder [[],[],[1,3,1],[2]]) (patternClique [[],[],[1,3,1],[2]]) (patternEdges [[],[],[1,3,1],[2]]) (patternAmount [[],[],[1,3,1],[2]]) (patternEdgeCount [[],[],[1,3,1],[2]]) [] := certificate_1992_checked

theorem certificate_1993_checked : certificate_1993.Valid 16 8 16 certificate_1993_q certificate_1993_edges 8 4 [] := by decide +kernel
theorem certificate_1993_valid : certificate_1993.Valid 16 8 (patternOrder [[],[],[1,3,1],[3]]) (patternClique [[],[],[1,3,1],[3]]) (patternEdges [[],[],[1,3,1],[3]]) (patternAmount [[],[],[1,3,1],[3]]) (patternEdgeCount [[],[],[1,3,1],[3]]) [] := certificate_1993_checked

theorem certificate_1994_checked : certificate_1994.Valid 16 8 16 certificate_1994_q certificate_1994_edges 8 5 [] := by decide +kernel
theorem certificate_1994_valid : certificate_1994.Valid 16 8 (patternOrder [[],[],[1,3,1,1,2]]) (patternClique [[],[],[1,3,1,1,2]]) (patternEdges [[],[],[1,3,1,1,2]]) (patternAmount [[],[],[1,3,1,1,2]]) (patternEdgeCount [[],[],[1,3,1,1,2]]) [] := certificate_1994_checked

theorem certificate_1995_checked : certificate_1995.Valid 16 8 16 certificate_1995_q certificate_1995_edges 8 4 [] := by decide +kernel
theorem certificate_1995_valid : certificate_1995.Valid 16 8 (patternOrder [[],[],[1,3,2],[2]]) (patternClique [[],[],[1,3,2],[2]]) (patternEdges [[],[],[1,3,2],[2]]) (patternAmount [[],[],[1,3,2],[2]]) (patternEdgeCount [[],[],[1,3,2],[2]]) [] := certificate_1995_checked

theorem certificate_1996_checked : certificate_1996.Valid 16 8 16 certificate_1996_q certificate_1996_edges 8 4 [] := by decide +kernel
theorem certificate_1996_valid : certificate_1996.Valid 16 8 (patternOrder [[],[],[1,4,1],[2]]) (patternClique [[],[],[1,4,1],[2]]) (patternEdges [[],[],[1,4,1],[2]]) (patternAmount [[],[],[1,4,1],[2]]) (patternEdgeCount [[],[],[1,4,1],[2]]) [] := certificate_1996_checked

theorem certificate_1997_checked : certificate_1997.Valid 16 8 14 certificate_1997_q certificate_1997_edges 6 3 [] := by decide +kernel
theorem certificate_1997_valid : certificate_1997.Valid 16 8 (patternOrder [[],[],[2],[2],[2]]) (patternClique [[],[],[2],[2],[2]]) (patternEdges [[],[],[2],[2],[2]]) (patternAmount [[],[],[2],[2],[2]]) (patternEdgeCount [[],[],[2],[2],[2]]) [] := certificate_1997_checked

theorem certificate_1998_checked : certificate_1998.Valid 16 8 15 certificate_1998_q certificate_1998_edges 7 3 [] := by decide +kernel
theorem certificate_1998_valid : certificate_1998.Valid 16 8 (patternOrder [[],[],[2],[2],[3]]) (patternClique [[],[],[2],[2],[3]]) (patternEdges [[],[],[2],[2],[3]]) (patternAmount [[],[],[2],[2],[3]]) (patternEdgeCount [[],[],[2],[2],[3]]) [] := certificate_1998_checked

theorem certificate_1999_checked : certificate_1999.Valid 16 8 16 certificate_1999_q certificate_1999_edges 8 3 [] := by decide +kernel
theorem certificate_1999_valid : certificate_1999.Valid 16 8 (patternOrder [[],[],[2],[2],[4]]) (patternClique [[],[],[2],[2],[4]]) (patternEdges [[],[],[2],[2],[4]]) (patternAmount [[],[],[2],[2],[4]]) (patternEdgeCount [[],[],[2],[2],[4]]) [] := certificate_1999_checked

theorem certificate_2000_checked : certificate_2000.Valid 16 8 15 certificate_2000_q certificate_2000_edges 7 4 [] := by decide +kernel
theorem certificate_2000_valid : certificate_2000.Valid 16 8 (patternOrder [[],[],[2],[2,1,2]]) (patternClique [[],[],[2],[2,1,2]]) (patternEdges [[],[],[2],[2,1,2]]) (patternAmount [[],[],[2],[2,1,2]]) (patternEdgeCount [[],[],[2],[2,1,2]]) [] := certificate_2000_checked

theorem certificate_2001_checked : certificate_2001.Valid 16 8 16 certificate_2001_q certificate_2001_edges 8 4 [] := by decide +kernel
theorem certificate_2001_valid : certificate_2001.Valid 16 8 (patternOrder [[],[],[2],[2,1,3]]) (patternClique [[],[],[2],[2,1,3]]) (patternEdges [[],[],[2],[2,1,3]]) (patternAmount [[],[],[2],[2,1,3]]) (patternEdgeCount [[],[],[2],[2,1,3]]) [] := certificate_2001_checked

theorem certificate_2002_checked : certificate_2002.Valid 16 8 16 certificate_2002_q certificate_2002_edges 8 4 [] := by decide +kernel
theorem certificate_2002_valid : certificate_2002.Valid 16 8 (patternOrder [[],[],[2],[2,2,2]]) (patternClique [[],[],[2],[2,2,2]]) (patternEdges [[],[],[2],[2,2,2]]) (patternAmount [[],[],[2],[2,2,2]]) (patternEdgeCount [[],[],[2],[2,2,2]]) [] := certificate_2002_checked

theorem certificate_2003_checked : certificate_2003.Valid 16 8 16 certificate_2003_q certificate_2003_edges 8 3 [] := by decide +kernel
theorem certificate_2003_valid : certificate_2003.Valid 16 8 (patternOrder [[],[],[2],[3],[3]]) (patternClique [[],[],[2],[3],[3]]) (patternEdges [[],[],[2],[3],[3]]) (patternAmount [[],[],[2],[3],[3]]) (patternEdgeCount [[],[],[2],[3],[3]]) [] := certificate_2003_checked

theorem certificate_2004_checked : certificate_2004.Valid 16 8 15 certificate_2004_q certificate_2004_edges 7 5 [] := by decide +kernel
theorem certificate_2004_valid : certificate_2004.Valid 16 8 (patternOrder [[],[],[2,1,1,1,2]]) (patternClique [[],[],[2,1,1,1,2]]) (patternEdges [[],[],[2,1,1,1,2]]) (patternAmount [[],[],[2,1,1,1,2]]) (patternEdgeCount [[],[],[2,1,1,1,2]]) [] := certificate_2004_checked

theorem certificate_2005_checked : certificate_2005.Valid 16 8 16 certificate_2005_q certificate_2005_edges 8 5 [] := by decide +kernel
theorem certificate_2005_valid : certificate_2005.Valid 16 8 (patternOrder [[],[],[2,1,1,1,3]]) (patternClique [[],[],[2,1,1,1,3]]) (patternEdges [[],[],[2,1,1,1,3]]) (patternAmount [[],[],[2,1,1,1,3]]) (patternEdgeCount [[],[],[2,1,1,1,3]]) [] := certificate_2005_checked

theorem certificate_2006_checked : certificate_2006.Valid 16 8 16 certificate_2006_q certificate_2006_edges 8 5 [] := by decide +kernel
theorem certificate_2006_valid : certificate_2006.Valid 16 8 (patternOrder [[],[],[2,1,1,2,2]]) (patternClique [[],[],[2,1,1,2,2]]) (patternEdges [[],[],[2,1,1,2,2]]) (patternAmount [[],[],[2,1,1,2,2]]) (patternEdgeCount [[],[],[2,1,1,2,2]]) [] := certificate_2006_checked

theorem certificate_2007_checked : certificate_2007.Valid 16 8 16 certificate_2007_q certificate_2007_edges 8 4 [] := by decide +kernel
theorem certificate_2007_valid : certificate_2007.Valid 16 8 (patternOrder [[],[],[2,1,2],[3]]) (patternClique [[],[],[2,1,2],[3]]) (patternEdges [[],[],[2,1,2],[3]]) (patternAmount [[],[],[2,1,2],[3]]) (patternEdgeCount [[],[],[2,1,2],[3]]) [] := certificate_2007_checked

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

theorem patterns_16_8_15_verified_oai : ∀ D ∈ patterns_16_8_15, PatternVerified 16 8 D := by

  simp only [patterns_16_8_15, List.forall_mem_cons]

  exact ⟨⟨certificate_1992, certificate_1992_valid⟩, ⟨⟨certificate_1993, certificate_1993_valid⟩, ⟨⟨certificate_1994, certificate_1994_valid⟩, ⟨⟨certificate_1995, certificate_1995_valid⟩, ⟨⟨certificate_1996, certificate_1996_valid⟩, ⟨⟨certificate_1997, certificate_1997_valid⟩, ⟨⟨certificate_1998, certificate_1998_valid⟩, ⟨⟨certificate_1999, certificate_1999_valid⟩, ⟨⟨certificate_2000, certificate_2000_valid⟩, ⟨⟨certificate_2001, certificate_2001_valid⟩, ⟨⟨certificate_2002, certificate_2002_valid⟩, ⟨⟨certificate_2003, certificate_2003_valid⟩, ⟨⟨certificate_2004, certificate_2004_valid⟩, ⟨⟨certificate_2005, certificate_2005_valid⟩, ⟨⟨certificate_2006, certificate_2006_valid⟩, ⟨⟨certificate_2007, certificate_2007_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_16_8_15_verified_oai := @OAI.CycleClique.patterns_16_8_15_verified_oai
