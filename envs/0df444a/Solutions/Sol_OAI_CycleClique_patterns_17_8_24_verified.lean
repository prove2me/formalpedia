-- Prove2me | solution 1 for OAI.CycleClique.patterns_17_8_24_verified
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:19:42.377565+00:00
-- url     : https://prove2.me/submissions/388580b3-d40b-483b-8607-6d12cf1192eb

import Mathlib
import Definitions.Def_OAIQ107D131
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates082
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2604_checked : certificate_2604.Valid 17 8 15 certificate_2604_q certificate_2604_edges 7 3 [] := by decide +kernel
theorem certificate_2604_valid : certificate_2604.Valid 17 8 (patternOrder [[],[],[2],[2],[3]]) (patternClique [[],[],[2],[2],[3]]) (patternEdges [[],[],[2],[2],[3]]) (patternAmount [[],[],[2],[2],[3]]) (patternEdgeCount [[],[],[2],[2],[3]]) [] := certificate_2604_checked

theorem certificate_2605_checked : certificate_2605.Valid 17 8 16 certificate_2605_q certificate_2605_edges 8 3 [] := by decide +kernel
theorem certificate_2605_valid : certificate_2605.Valid 17 8 (patternOrder [[],[],[2],[2],[4]]) (patternClique [[],[],[2],[2],[4]]) (patternEdges [[],[],[2],[2],[4]]) (patternAmount [[],[],[2],[2],[4]]) (patternEdgeCount [[],[],[2],[2],[4]]) [] := certificate_2605_checked

theorem certificate_2606_checked : certificate_2606.Valid 17 8 17 certificate_2606_q certificate_2606_edges 9 3 [] := by decide +kernel
theorem certificate_2606_valid : certificate_2606.Valid 17 8 (patternOrder [[],[],[2],[2],[5]]) (patternClique [[],[],[2],[2],[5]]) (patternEdges [[],[],[2],[2],[5]]) (patternAmount [[],[],[2],[2],[5]]) (patternEdgeCount [[],[],[2],[2],[5]]) [] := certificate_2606_checked

theorem certificate_2607_checked : certificate_2607.Valid 17 8 15 certificate_2607_q certificate_2607_edges 7 4 [] := by decide +kernel
theorem certificate_2607_valid : certificate_2607.Valid 17 8 (patternOrder [[],[],[2],[2,1,2]]) (patternClique [[],[],[2],[2,1,2]]) (patternEdges [[],[],[2],[2,1,2]]) (patternAmount [[],[],[2],[2,1,2]]) (patternEdgeCount [[],[],[2],[2,1,2]]) [] := certificate_2607_checked

theorem certificate_2608_checked : certificate_2608.Valid 17 8 16 certificate_2608_q certificate_2608_edges 8 4 [] := by decide +kernel
theorem certificate_2608_valid : certificate_2608.Valid 17 8 (patternOrder [[],[],[2],[2,1,3]]) (patternClique [[],[],[2],[2,1,3]]) (patternEdges [[],[],[2],[2,1,3]]) (patternAmount [[],[],[2],[2,1,3]]) (patternEdgeCount [[],[],[2],[2,1,3]]) [] := certificate_2608_checked

theorem certificate_2609_checked : certificate_2609.Valid 17 8 17 certificate_2609_q certificate_2609_edges 9 4 [] := by decide +kernel
theorem certificate_2609_valid : certificate_2609.Valid 17 8 (patternOrder [[],[],[2],[2,1,4]]) (patternClique [[],[],[2],[2,1,4]]) (patternEdges [[],[],[2],[2,1,4]]) (patternAmount [[],[],[2],[2,1,4]]) (patternEdgeCount [[],[],[2],[2,1,4]]) [] := certificate_2609_checked

theorem certificate_2610_checked : certificate_2610.Valid 17 8 16 certificate_2610_q certificate_2610_edges 8 4 [] := by decide +kernel
theorem certificate_2610_valid : certificate_2610.Valid 17 8 (patternOrder [[],[],[2],[2,2,2]]) (patternClique [[],[],[2],[2,2,2]]) (patternEdges [[],[],[2],[2,2,2]]) (patternAmount [[],[],[2],[2,2,2]]) (patternEdgeCount [[],[],[2],[2,2,2]]) [] := certificate_2610_checked

theorem certificate_2611_checked : certificate_2611.Valid 17 8 17 certificate_2611_q certificate_2611_edges 9 4 [] := by decide +kernel
theorem certificate_2611_valid : certificate_2611.Valid 17 8 (patternOrder [[],[],[2],[2,2,3]]) (patternClique [[],[],[2],[2,2,3]]) (patternEdges [[],[],[2],[2,2,3]]) (patternAmount [[],[],[2],[2,2,3]]) (patternEdgeCount [[],[],[2],[2,2,3]]) [] := certificate_2611_checked

theorem certificate_2612_checked : certificate_2612.Valid 17 8 17 certificate_2612_q certificate_2612_edges 9 4 [] := by decide +kernel
theorem certificate_2612_valid : certificate_2612.Valid 17 8 (patternOrder [[],[],[2],[2,3,2]]) (patternClique [[],[],[2],[2,3,2]]) (patternEdges [[],[],[2],[2,3,2]]) (patternAmount [[],[],[2],[2,3,2]]) (patternEdgeCount [[],[],[2],[2,3,2]]) [] := certificate_2612_checked

theorem certificate_2613_checked : certificate_2613.Valid 17 8 16 certificate_2613_q certificate_2613_edges 8 3 [] := by decide +kernel
theorem certificate_2613_valid : certificate_2613.Valid 17 8 (patternOrder [[],[],[2],[3],[3]]) (patternClique [[],[],[2],[3],[3]]) (patternEdges [[],[],[2],[3],[3]]) (patternAmount [[],[],[2],[3],[3]]) (patternEdgeCount [[],[],[2],[3],[3]]) [] := certificate_2613_checked

theorem certificate_2614_checked : certificate_2614.Valid 17 8 17 certificate_2614_q certificate_2614_edges 9 3 [] := by decide +kernel
theorem certificate_2614_valid : certificate_2614.Valid 17 8 (patternOrder [[],[],[2],[3],[4]]) (patternClique [[],[],[2],[3],[4]]) (patternEdges [[],[],[2],[3],[4]]) (patternAmount [[],[],[2],[3],[4]]) (patternEdgeCount [[],[],[2],[3],[4]]) [] := certificate_2614_checked

theorem certificate_2615_checked : certificate_2615.Valid 17 8 17 certificate_2615_q certificate_2615_edges 9 4 [] := by decide +kernel
theorem certificate_2615_valid : certificate_2615.Valid 17 8 (patternOrder [[],[],[2],[3,1,3]]) (patternClique [[],[],[2],[3,1,3]]) (patternEdges [[],[],[2],[3,1,3]]) (patternAmount [[],[],[2],[3,1,3]]) (patternEdgeCount [[],[],[2],[3,1,3]]) [] := certificate_2615_checked

theorem certificate_2616_checked : certificate_2616.Valid 17 8 15 certificate_2616_q certificate_2616_edges 7 5 [] := by decide +kernel
theorem certificate_2616_valid : certificate_2616.Valid 17 8 (patternOrder [[],[],[2,1,1,1,2]]) (patternClique [[],[],[2,1,1,1,2]]) (patternEdges [[],[],[2,1,1,1,2]]) (patternAmount [[],[],[2,1,1,1,2]]) (patternEdgeCount [[],[],[2,1,1,1,2]]) [] := certificate_2616_checked

theorem certificate_2617_checked : certificate_2617.Valid 17 8 16 certificate_2617_q certificate_2617_edges 8 5 [] := by decide +kernel
theorem certificate_2617_valid : certificate_2617.Valid 17 8 (patternOrder [[],[],[2,1,1,1,3]]) (patternClique [[],[],[2,1,1,1,3]]) (patternEdges [[],[],[2,1,1,1,3]]) (patternAmount [[],[],[2,1,1,1,3]]) (patternEdgeCount [[],[],[2,1,1,1,3]]) [] := certificate_2617_checked

theorem certificate_2618_checked : certificate_2618.Valid 17 8 17 certificate_2618_q certificate_2618_edges 9 5 [] := by decide +kernel
theorem certificate_2618_valid : certificate_2618.Valid 17 8 (patternOrder [[],[],[2,1,1,1,4]]) (patternClique [[],[],[2,1,1,1,4]]) (patternEdges [[],[],[2,1,1,1,4]]) (patternAmount [[],[],[2,1,1,1,4]]) (patternEdgeCount [[],[],[2,1,1,1,4]]) [] := certificate_2618_checked

theorem certificate_2619_checked : certificate_2619.Valid 17 8 16 certificate_2619_q certificate_2619_edges 8 5 [] := by decide +kernel
theorem certificate_2619_valid : certificate_2619.Valid 17 8 (patternOrder [[],[],[2,1,1,2,2]]) (patternClique [[],[],[2,1,1,2,2]]) (patternEdges [[],[],[2,1,1,2,2]]) (patternAmount [[],[],[2,1,1,2,2]]) (patternEdgeCount [[],[],[2,1,1,2,2]]) [] := certificate_2619_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns17x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_17_8_24_verified_oai : ∀ D ∈ patterns_17_8_24, PatternVerified 17 8 D := by

  simp only [patterns_17_8_24, List.forall_mem_cons]

  exact ⟨⟨certificate_2604, certificate_2604_valid⟩, ⟨⟨certificate_2605, certificate_2605_valid⟩, ⟨⟨certificate_2606, certificate_2606_valid⟩, ⟨⟨certificate_2607, certificate_2607_valid⟩, ⟨⟨certificate_2608, certificate_2608_valid⟩, ⟨⟨certificate_2609, certificate_2609_valid⟩, ⟨⟨certificate_2610, certificate_2610_valid⟩, ⟨⟨certificate_2611, certificate_2611_valid⟩, ⟨⟨certificate_2612, certificate_2612_valid⟩, ⟨⟨certificate_2613, certificate_2613_valid⟩, ⟨⟨certificate_2614, certificate_2614_valid⟩, ⟨⟨certificate_2615, certificate_2615_valid⟩, ⟨⟨certificate_2616, certificate_2616_valid⟩, ⟨⟨certificate_2617, certificate_2617_valid⟩, ⟨⟨certificate_2618, certificate_2618_valid⟩, ⟨⟨certificate_2619, certificate_2619_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.patterns_17_8_24_verified_oai := @OAI.CycleClique.patterns_17_8_24_verified_oai
