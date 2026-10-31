-- Prove2me | solution 1 for OAI.CycleClique.finite_patterns_12_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T20:26:52.583607+00:00
-- url     : https://prove2.me/submissions/878e0254-c2f1-4c94-b76a-f9adf95bd6e0

import Mathlib
import Definitions.Def_OAIQ107D132
import Definitions.Def_OAIQ107D133

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates015
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_448_checked : certificate_448.Valid 12 7 7 certificate_448_q certificate_448_edges 0 0 [] := by decide +kernel
theorem certificate_448_valid : certificate_448.Valid 12 7 (patternOrder [[],[],[],[],[],[],[]]) (patternClique [[],[],[],[],[],[],[]]) (patternEdges [[],[],[],[],[],[],[]]) (patternAmount [[],[],[],[],[],[],[]]) (patternEdgeCount [[],[],[],[],[],[],[]]) [] := certificate_448_checked

theorem certificate_449_checked : certificate_449.Valid 12 7 8 certificate_449_q certificate_449_edges 1 1 [] := by decide +kernel
theorem certificate_449_valid : certificate_449.Valid 12 7 (patternOrder [[],[],[],[],[],[1]]) (patternClique [[],[],[],[],[],[1]]) (patternEdges [[],[],[],[],[],[1]]) (patternAmount [[],[],[],[],[],[1]]) (patternEdgeCount [[],[],[],[],[],[1]]) [] := certificate_449_checked

theorem certificate_450_checked : certificate_450.Valid 12 7 9 certificate_450_q certificate_450_edges 2 1 [] := by decide +kernel
theorem certificate_450_valid : certificate_450.Valid 12 7 (patternOrder [[],[],[],[],[],[2]]) (patternClique [[],[],[],[],[],[2]]) (patternEdges [[],[],[],[],[],[2]]) (patternAmount [[],[],[],[],[],[2]]) (patternEdgeCount [[],[],[],[],[],[2]]) [] := certificate_450_checked

theorem certificate_451_checked : certificate_451.Valid 12 7 10 certificate_451_q certificate_451_edges 3 1 [] := by decide +kernel
theorem certificate_451_valid : certificate_451.Valid 12 7 (patternOrder [[],[],[],[],[],[3]]) (patternClique [[],[],[],[],[],[3]]) (patternEdges [[],[],[],[],[],[3]]) (patternAmount [[],[],[],[],[],[3]]) (patternEdgeCount [[],[],[],[],[],[3]]) [] := certificate_451_checked

theorem certificate_452_checked : certificate_452.Valid 12 7 11 certificate_452_q certificate_452_edges 4 1 [] := by decide +kernel
theorem certificate_452_valid : certificate_452.Valid 12 7 (patternOrder [[],[],[],[],[],[4]]) (patternClique [[],[],[],[],[],[4]]) (patternEdges [[],[],[],[],[],[4]]) (patternAmount [[],[],[],[],[],[4]]) (patternEdgeCount [[],[],[],[],[],[4]]) [] := certificate_452_checked

theorem certificate_453_checked : certificate_453.Valid 12 7 12 certificate_453_q certificate_453_edges 5 1 [] := by decide +kernel
theorem certificate_453_valid : certificate_453.Valid 12 7 (patternOrder [[],[],[],[],[],[5]]) (patternClique [[],[],[],[],[],[5]]) (patternEdges [[],[],[],[],[],[5]]) (patternAmount [[],[],[],[],[],[5]]) (patternEdgeCount [[],[],[],[],[],[5]]) [] := certificate_453_checked

theorem certificate_454_checked : certificate_454.Valid 12 7 9 certificate_454_q certificate_454_edges 2 2 [] := by decide +kernel
theorem certificate_454_valid : certificate_454.Valid 12 7 (patternOrder [[],[],[],[],[1,1]]) (patternClique [[],[],[],[],[1,1]]) (patternEdges [[],[],[],[],[1,1]]) (patternAmount [[],[],[],[],[1,1]]) (patternEdgeCount [[],[],[],[],[1,1]]) [] := certificate_454_checked

theorem certificate_455_checked : certificate_455.Valid 12 7 10 certificate_455_q certificate_455_edges 3 2 [] := by decide +kernel
theorem certificate_455_valid : certificate_455.Valid 12 7 (patternOrder [[],[],[],[],[1,2]]) (patternClique [[],[],[],[],[1,2]]) (patternEdges [[],[],[],[],[1,2]]) (patternAmount [[],[],[],[],[1,2]]) (patternEdgeCount [[],[],[],[],[1,2]]) [] := certificate_455_checked

theorem certificate_456_checked : certificate_456.Valid 12 7 11 certificate_456_q certificate_456_edges 4 2 [] := by decide +kernel
theorem certificate_456_valid : certificate_456.Valid 12 7 (patternOrder [[],[],[],[],[1,3]]) (patternClique [[],[],[],[],[1,3]]) (patternEdges [[],[],[],[],[1,3]]) (patternAmount [[],[],[],[],[1,3]]) (patternEdgeCount [[],[],[],[],[1,3]]) [] := certificate_456_checked

theorem certificate_457_checked : certificate_457.Valid 12 7 12 certificate_457_q certificate_457_edges 5 2 [] := by decide +kernel
theorem certificate_457_valid : certificate_457.Valid 12 7 (patternOrder [[],[],[],[],[1,4]]) (patternClique [[],[],[],[],[1,4]]) (patternEdges [[],[],[],[],[1,4]]) (patternAmount [[],[],[],[],[1,4]]) (patternEdgeCount [[],[],[],[],[1,4]]) [] := certificate_457_checked

theorem certificate_458_checked : certificate_458.Valid 12 7 11 certificate_458_q certificate_458_edges 4 2 [] := by decide +kernel
theorem certificate_458_valid : certificate_458.Valid 12 7 (patternOrder [[],[],[],[],[2,2]]) (patternClique [[],[],[],[],[2,2]]) (patternEdges [[],[],[],[],[2,2]]) (patternAmount [[],[],[],[],[2,2]]) (patternEdgeCount [[],[],[],[],[2,2]]) [] := certificate_458_checked

theorem certificate_459_checked : certificate_459.Valid 12 7 12 certificate_459_q certificate_459_edges 5 2 [] := by decide +kernel
theorem certificate_459_valid : certificate_459.Valid 12 7 (patternOrder [[],[],[],[],[2,3]]) (patternClique [[],[],[],[],[2,3]]) (patternEdges [[],[],[],[],[2,3]]) (patternAmount [[],[],[],[],[2,3]]) (patternEdgeCount [[],[],[],[],[2,3]]) [] := certificate_459_checked

theorem certificate_460_checked : certificate_460.Valid 12 7 9 certificate_460_q certificate_460_edges 2 2 [] := by decide +kernel
theorem certificate_460_valid : certificate_460.Valid 12 7 (patternOrder [[],[],[],[1],[1]]) (patternClique [[],[],[],[1],[1]]) (patternEdges [[],[],[],[1],[1]]) (patternAmount [[],[],[],[1],[1]]) (patternEdgeCount [[],[],[],[1],[1]]) [] := certificate_460_checked

theorem certificate_461_checked : certificate_461.Valid 12 7 10 certificate_461_q certificate_461_edges 3 2 [] := by decide +kernel
theorem certificate_461_valid : certificate_461.Valid 12 7 (patternOrder [[],[],[],[1],[2]]) (patternClique [[],[],[],[1],[2]]) (patternEdges [[],[],[],[1],[2]]) (patternAmount [[],[],[],[1],[2]]) (patternEdgeCount [[],[],[],[1],[2]]) [] := certificate_461_checked

theorem certificate_462_checked : certificate_462.Valid 12 7 11 certificate_462_q certificate_462_edges 4 2 [] := by decide +kernel
theorem certificate_462_valid : certificate_462.Valid 12 7 (patternOrder [[],[],[],[1],[3]]) (patternClique [[],[],[],[1],[3]]) (patternEdges [[],[],[],[1],[3]]) (patternAmount [[],[],[],[1],[3]]) (patternEdgeCount [[],[],[],[1],[3]]) [] := certificate_462_checked

theorem certificate_463_checked : certificate_463.Valid 12 7 12 certificate_463_q certificate_463_edges 5 2 [] := by decide +kernel
theorem certificate_463_valid : certificate_463.Valid 12 7 (patternOrder [[],[],[],[1],[4]]) (patternClique [[],[],[],[1],[4]]) (patternEdges [[],[],[],[1],[4]]) (patternAmount [[],[],[],[1],[4]]) (patternEdgeCount [[],[],[],[1],[4]]) [] := certificate_463_checked

theorem certificate_464_checked : certificate_464.Valid 12 7 10 certificate_464_q certificate_464_edges 3 3 [] := by decide +kernel
theorem certificate_464_valid : certificate_464.Valid 12 7 (patternOrder [[],[],[],[1,1,1]]) (patternClique [[],[],[],[1,1,1]]) (patternEdges [[],[],[],[1,1,1]]) (patternAmount [[],[],[],[1,1,1]]) (patternEdgeCount [[],[],[],[1,1,1]]) [] := certificate_464_checked

theorem certificate_465_checked : certificate_465.Valid 12 7 11 certificate_465_q certificate_465_edges 4 3 [] := by decide +kernel
theorem certificate_465_valid : certificate_465.Valid 12 7 (patternOrder [[],[],[],[1,1,2]]) (patternClique [[],[],[],[1,1,2]]) (patternEdges [[],[],[],[1,1,2]]) (patternAmount [[],[],[],[1,1,2]]) (patternEdgeCount [[],[],[],[1,1,2]]) [] := certificate_465_checked

theorem certificate_466_checked : certificate_466.Valid 12 7 12 certificate_466_q certificate_466_edges 5 3 [] := by decide +kernel
theorem certificate_466_valid : certificate_466.Valid 12 7 (patternOrder [[],[],[],[1,1,3]]) (patternClique [[],[],[],[1,1,3]]) (patternEdges [[],[],[],[1,1,3]]) (patternAmount [[],[],[],[1,1,3]]) (patternEdgeCount [[],[],[],[1,1,3]]) [] := certificate_466_checked

theorem certificate_467_checked : certificate_467.Valid 12 7 11 certificate_467_q certificate_467_edges 4 3 [] := by decide +kernel
theorem certificate_467_valid : certificate_467.Valid 12 7 (patternOrder [[],[],[],[1,2,1]]) (patternClique [[],[],[],[1,2,1]]) (patternEdges [[],[],[],[1,2,1]]) (patternAmount [[],[],[],[1,2,1]]) (patternEdgeCount [[],[],[],[1,2,1]]) [] := certificate_467_checked

theorem certificate_468_checked : certificate_468.Valid 12 7 12 certificate_468_q certificate_468_edges 5 3 [] := by decide +kernel
theorem certificate_468_valid : certificate_468.Valid 12 7 (patternOrder [[],[],[],[1,2,2]]) (patternClique [[],[],[],[1,2,2]]) (patternEdges [[],[],[],[1,2,2]]) (patternAmount [[],[],[],[1,2,2]]) (patternEdgeCount [[],[],[],[1,2,2]]) [] := certificate_468_checked

theorem certificate_469_checked : certificate_469.Valid 12 7 12 certificate_469_q certificate_469_edges 5 3 [] := by decide +kernel
theorem certificate_469_valid : certificate_469.Valid 12 7 (patternOrder [[],[],[],[1,3,1]]) (patternClique [[],[],[],[1,3,1]]) (patternEdges [[],[],[],[1,3,1]]) (patternAmount [[],[],[],[1,3,1]]) (patternEdgeCount [[],[],[],[1,3,1]]) [] := certificate_469_checked

theorem certificate_470_checked : certificate_470.Valid 12 7 11 certificate_470_q certificate_470_edges 4 2 [] := by decide +kernel
theorem certificate_470_valid : certificate_470.Valid 12 7 (patternOrder [[],[],[],[2],[2]]) (patternClique [[],[],[],[2],[2]]) (patternEdges [[],[],[],[2],[2]]) (patternAmount [[],[],[],[2],[2]]) (patternEdgeCount [[],[],[],[2],[2]]) [] := certificate_470_checked

theorem certificate_471_checked : certificate_471.Valid 12 7 12 certificate_471_q certificate_471_edges 5 2 [] := by decide +kernel
theorem certificate_471_valid : certificate_471.Valid 12 7 (patternOrder [[],[],[],[2],[3]]) (patternClique [[],[],[],[2],[3]]) (patternEdges [[],[],[],[2],[3]]) (patternAmount [[],[],[],[2],[3]]) (patternEdgeCount [[],[],[],[2],[3]]) [] := certificate_471_checked

theorem certificate_472_checked : certificate_472.Valid 12 7 12 certificate_472_q certificate_472_edges 5 3 [] := by decide +kernel
theorem certificate_472_valid : certificate_472.Valid 12 7 (patternOrder [[],[],[],[2,1,2]]) (patternClique [[],[],[],[2,1,2]]) (patternEdges [[],[],[],[2,1,2]]) (patternAmount [[],[],[],[2,1,2]]) (patternEdgeCount [[],[],[],[2,1,2]]) [] := certificate_472_checked

theorem certificate_473_checked : certificate_473.Valid 12 7 10 certificate_473_q certificate_473_edges 3 3 [] := by decide +kernel
theorem certificate_473_valid : certificate_473.Valid 12 7 (patternOrder [[],[],[1],[1,1]]) (patternClique [[],[],[1],[1,1]]) (patternEdges [[],[],[1],[1,1]]) (patternAmount [[],[],[1],[1,1]]) (patternEdgeCount [[],[],[1],[1,1]]) [] := certificate_473_checked

theorem certificate_474_checked : certificate_474.Valid 12 7 11 certificate_474_q certificate_474_edges 4 3 [] := by decide +kernel
theorem certificate_474_valid : certificate_474.Valid 12 7 (patternOrder [[],[],[1],[1,2]]) (patternClique [[],[],[1],[1,2]]) (patternEdges [[],[],[1],[1,2]]) (patternAmount [[],[],[1],[1,2]]) (patternEdgeCount [[],[],[1],[1,2]]) [] := certificate_474_checked

theorem certificate_475_checked : certificate_475.Valid 12 7 12 certificate_475_q certificate_475_edges 5 3 [] := by decide +kernel
theorem certificate_475_valid : certificate_475.Valid 12 7 (patternOrder [[],[],[1],[1,3]]) (patternClique [[],[],[1],[1,3]]) (patternEdges [[],[],[1],[1,3]]) (patternAmount [[],[],[1],[1,3]]) (patternEdgeCount [[],[],[1],[1,3]]) [] := certificate_475_checked

theorem certificate_476_checked : certificate_476.Valid 12 7 12 certificate_476_q certificate_476_edges 5 3 [] := by decide +kernel
theorem certificate_476_valid : certificate_476.Valid 12 7 (patternOrder [[],[],[1],[2,2]]) (patternClique [[],[],[1],[2,2]]) (patternEdges [[],[],[1],[2,2]]) (patternAmount [[],[],[1],[2,2]]) (patternEdgeCount [[],[],[1],[2,2]]) [] := certificate_476_checked

theorem certificate_477_checked : certificate_477.Valid 12 7 11 certificate_477_q certificate_477_edges 4 3 [] := by decide +kernel
theorem certificate_477_valid : certificate_477.Valid 12 7 (patternOrder [[],[],[1,1],[2]]) (patternClique [[],[],[1,1],[2]]) (patternEdges [[],[],[1,1],[2]]) (patternAmount [[],[],[1,1],[2]]) (patternEdgeCount [[],[],[1,1],[2]]) [] := certificate_477_checked

theorem certificate_478_checked : certificate_478.Valid 12 7 12 certificate_478_q certificate_478_edges 5 3 [] := by decide +kernel
theorem certificate_478_valid : certificate_478.Valid 12 7 (patternOrder [[],[],[1,1],[3]]) (patternClique [[],[],[1,1],[3]]) (patternEdges [[],[],[1,1],[3]]) (patternAmount [[],[],[1,1],[3]]) (patternEdgeCount [[],[],[1,1],[3]]) [] := certificate_478_checked

theorem certificate_479_checked : certificate_479.Valid 12 7 11 certificate_479_q certificate_479_edges 4 4 [] := by decide +kernel
theorem certificate_479_valid : certificate_479.Valid 12 7 (patternOrder [[],[],[1,1,1,1]]) (patternClique [[],[],[1,1,1,1]]) (patternEdges [[],[],[1,1,1,1]]) (patternAmount [[],[],[1,1,1,1]]) (patternEdgeCount [[],[],[1,1,1,1]]) [] := certificate_479_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates016
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_480_checked : certificate_480.Valid 12 7 12 certificate_480_q certificate_480_edges 5 4 [] := by decide +kernel
theorem certificate_480_valid : certificate_480.Valid 12 7 (patternOrder [[],[],[1,1,1,2]]) (patternClique [[],[],[1,1,1,2]]) (patternEdges [[],[],[1,1,1,2]]) (patternAmount [[],[],[1,1,1,2]]) (patternEdgeCount [[],[],[1,1,1,2]]) [] := certificate_480_checked

theorem certificate_481_checked : certificate_481.Valid 12 7 12 certificate_481_q certificate_481_edges 5 4 [] := by decide +kernel
theorem certificate_481_valid : certificate_481.Valid 12 7 (patternOrder [[],[],[1,1,2,1]]) (patternClique [[],[],[1,1,2,1]]) (patternEdges [[],[],[1,1,2,1]]) (patternAmount [[],[],[1,1,2,1]]) (patternEdgeCount [[],[],[1,1,2,1]]) [] := certificate_481_checked

theorem certificate_482_checked : certificate_482.Valid 12 7 12 certificate_482_q certificate_482_edges 5 3 [] := by decide +kernel
theorem certificate_482_valid : certificate_482.Valid 12 7 (patternOrder [[],[],[1,2],[2]]) (patternClique [[],[],[1,2],[2]]) (patternEdges [[],[],[1,2],[2]]) (patternAmount [[],[],[1,2],[2]]) (patternEdgeCount [[],[],[1,2],[2]]) [] := certificate_482_checked

theorem certificate_483_checked : certificate_483.Valid 12 7 10 certificate_483_q certificate_483_edges 3 3 [] := by decide +kernel
theorem certificate_483_valid : certificate_483.Valid 12 7 (patternOrder [[],[1],[1],[1]]) (patternClique [[],[1],[1],[1]]) (patternEdges [[],[1],[1],[1]]) (patternAmount [[],[1],[1],[1]]) (patternEdgeCount [[],[1],[1],[1]]) [] := certificate_483_checked

theorem certificate_484_checked : certificate_484.Valid 12 7 11 certificate_484_q certificate_484_edges 4 3 [] := by decide +kernel
theorem certificate_484_valid : certificate_484.Valid 12 7 (patternOrder [[],[1],[1],[2]]) (patternClique [[],[1],[1],[2]]) (patternEdges [[],[1],[1],[2]]) (patternAmount [[],[1],[1],[2]]) (patternEdgeCount [[],[1],[1],[2]]) [] := certificate_484_checked

theorem certificate_485_checked : certificate_485.Valid 12 7 12 certificate_485_q certificate_485_edges 5 3 [] := by decide +kernel
theorem certificate_485_valid : certificate_485.Valid 12 7 (patternOrder [[],[1],[1],[3]]) (patternClique [[],[1],[1],[3]]) (patternEdges [[],[1],[1],[3]]) (patternAmount [[],[1],[1],[3]]) (patternEdgeCount [[],[1],[1],[3]]) [] := certificate_485_checked

theorem certificate_486_checked : certificate_486.Valid 12 7 11 certificate_486_q certificate_486_edges 4 4 [] := by decide +kernel
theorem certificate_486_valid : certificate_486.Valid 12 7 (patternOrder [[],[1],[1,1,1]]) (patternClique [[],[1],[1,1,1]]) (patternEdges [[],[1],[1,1,1]]) (patternAmount [[],[1],[1,1,1]]) (patternEdgeCount [[],[1],[1,1,1]]) [] := certificate_486_checked

theorem certificate_487_checked : certificate_487.Valid 12 7 12 certificate_487_q certificate_487_edges 5 4 [] := by decide +kernel
theorem certificate_487_valid : certificate_487.Valid 12 7 (patternOrder [[],[1],[1,1,2]]) (patternClique [[],[1],[1,1,2]]) (patternEdges [[],[1],[1,1,2]]) (patternAmount [[],[1],[1,1,2]]) (patternEdgeCount [[],[1],[1,1,2]]) [] := certificate_487_checked

theorem certificate_488_checked : certificate_488.Valid 12 7 12 certificate_488_q certificate_488_edges 5 4 [] := by decide +kernel
theorem certificate_488_valid : certificate_488.Valid 12 7 (patternOrder [[],[1],[1,2,1]]) (patternClique [[],[1],[1,2,1]]) (patternEdges [[],[1],[1,2,1]]) (patternAmount [[],[1],[1,2,1]]) (patternEdgeCount [[],[1],[1,2,1]]) [] := certificate_488_checked

theorem certificate_489_checked : certificate_489.Valid 12 7 12 certificate_489_q certificate_489_edges 5 3 [] := by decide +kernel
theorem certificate_489_valid : certificate_489.Valid 12 7 (patternOrder [[],[1],[2],[2]]) (patternClique [[],[1],[2],[2]]) (patternEdges [[],[1],[2],[2]]) (patternAmount [[],[1],[2],[2]]) (patternEdgeCount [[],[1],[2],[2]]) [] := certificate_489_checked

theorem certificate_490_checked : certificate_490.Valid 12 7 11 certificate_490_q certificate_490_edges 4 4 [] := by decide +kernel
theorem certificate_490_valid : certificate_490.Valid 12 7 (patternOrder [[],[1,1],[1,1]]) (patternClique [[],[1,1],[1,1]]) (patternEdges [[],[1,1],[1,1]]) (patternAmount [[],[1,1],[1,1]]) (patternEdgeCount [[],[1,1],[1,1]]) [] := certificate_490_checked

theorem certificate_491_checked : certificate_491.Valid 12 7 12 certificate_491_q certificate_491_edges 5 4 [] := by decide +kernel
theorem certificate_491_valid : certificate_491.Valid 12 7 (patternOrder [[],[1,1],[1,2]]) (patternClique [[],[1,1],[1,2]]) (patternEdges [[],[1,1],[1,2]]) (patternAmount [[],[1,1],[1,2]]) (patternEdgeCount [[],[1,1],[1,2]]) [] := certificate_491_checked

theorem certificate_492_checked : certificate_492.Valid 12 7 12 certificate_492_q certificate_492_edges 5 4 [] := by decide +kernel
theorem certificate_492_valid : certificate_492.Valid 12 7 (patternOrder [[],[1,1,1],[2]]) (patternClique [[],[1,1,1],[2]]) (patternEdges [[],[1,1,1],[2]]) (patternAmount [[],[1,1,1],[2]]) (patternEdgeCount [[],[1,1,1],[2]]) [] := certificate_492_checked

theorem certificate_493_checked : certificate_493.Valid 12 7 12 certificate_493_q certificate_493_edges 5 5 [] := by decide +kernel
theorem certificate_493_valid : certificate_493.Valid 12 7 (patternOrder [[],[1,1,1,1,1]]) (patternClique [[],[1,1,1,1,1]]) (patternEdges [[],[1,1,1,1,1]]) (patternAmount [[],[1,1,1,1,1]]) (patternEdgeCount [[],[1,1,1,1,1]]) [] := certificate_493_checked

theorem certificate_494_checked : certificate_494.Valid 12 7 11 certificate_494_q certificate_494_edges 4 4 [] := by decide +kernel
theorem certificate_494_valid : certificate_494.Valid 12 7 (patternOrder [[1],[1],[1,1]]) (patternClique [[1],[1],[1,1]]) (patternEdges [[1],[1],[1,1]]) (patternAmount [[1],[1],[1,1]]) (patternEdgeCount [[1],[1],[1,1]]) [] := certificate_494_checked

theorem certificate_495_checked : certificate_495.Valid 12 7 12 certificate_495_q certificate_495_edges 5 4 [] := by decide +kernel
theorem certificate_495_valid : certificate_495.Valid 12 7 (patternOrder [[1],[1],[1,2]]) (patternClique [[1],[1],[1,2]]) (patternEdges [[1],[1],[1,2]]) (patternAmount [[1],[1],[1,2]]) (patternEdgeCount [[1],[1],[1,2]]) [] := certificate_495_checked

theorem certificate_496_checked : certificate_496.Valid 12 7 12 certificate_496_q certificate_496_edges 5 4 [] := by decide +kernel
theorem certificate_496_valid : certificate_496.Valid 12 7 (patternOrder [[1],[1,1],[2]]) (patternClique [[1],[1,1],[2]]) (patternEdges [[1],[1,1],[2]]) (patternAmount [[1],[1,1],[2]]) (patternEdgeCount [[1],[1,1],[2]]) [] := certificate_496_checked

theorem certificate_497_checked : certificate_497.Valid 12 7 12 certificate_497_q certificate_497_edges 5 5 [] := by decide +kernel
theorem certificate_497_valid : certificate_497.Valid 12 7 (patternOrder [[1],[1,1,1,1]]) (patternClique [[1],[1,1,1,1]]) (patternEdges [[1],[1,1,1,1]]) (patternAmount [[1],[1,1,1,1]]) (patternEdgeCount [[1],[1,1,1,1]]) [] := certificate_497_checked

theorem certificate_498_checked : certificate_498.Valid 12 7 12 certificate_498_q certificate_498_edges 5 5 [] := by decide +kernel
theorem certificate_498_valid : certificate_498.Valid 12 7 (patternOrder [[1,1],[1,1,1]]) (patternClique [[1,1],[1,1,1]]) (patternEdges [[1,1],[1,1,1]]) (patternAmount [[1,1],[1,1,1]]) (patternEdgeCount [[1,1],[1,1,1]]) [] := certificate_498_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns12x7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_12_7_0_verified : ∀ D ∈ patterns_12_7_0, PatternVerified 12 7 D := by

  simp only [patterns_12_7_0, List.forall_mem_cons]

  exact ⟨⟨certificate_448, certificate_448_valid⟩, ⟨⟨certificate_449, certificate_449_valid⟩, ⟨⟨certificate_450, certificate_450_valid⟩, ⟨⟨certificate_451, certificate_451_valid⟩, ⟨⟨certificate_452, certificate_452_valid⟩, ⟨⟨certificate_453, certificate_453_valid⟩, ⟨⟨certificate_454, certificate_454_valid⟩, ⟨⟨certificate_455, certificate_455_valid⟩, ⟨⟨certificate_456, certificate_456_valid⟩, ⟨⟨certificate_457, certificate_457_valid⟩, ⟨⟨certificate_458, certificate_458_valid⟩, ⟨⟨certificate_459, certificate_459_valid⟩, ⟨⟨certificate_460, certificate_460_valid⟩, ⟨⟨certificate_461, certificate_461_valid⟩, ⟨⟨certificate_462, certificate_462_valid⟩, ⟨⟨certificate_463, certificate_463_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_12_7_1_verified : ∀ D ∈ patterns_12_7_1, PatternVerified 12 7 D := by

  simp only [patterns_12_7_1, List.forall_mem_cons]

  exact ⟨⟨certificate_464, certificate_464_valid⟩, ⟨⟨certificate_465, certificate_465_valid⟩, ⟨⟨certificate_466, certificate_466_valid⟩, ⟨⟨certificate_467, certificate_467_valid⟩, ⟨⟨certificate_468, certificate_468_valid⟩, ⟨⟨certificate_469, certificate_469_valid⟩, ⟨⟨certificate_470, certificate_470_valid⟩, ⟨⟨certificate_471, certificate_471_valid⟩, ⟨⟨certificate_472, certificate_472_valid⟩, ⟨⟨certificate_473, certificate_473_valid⟩, ⟨⟨certificate_474, certificate_474_valid⟩, ⟨⟨certificate_475, certificate_475_valid⟩, ⟨⟨certificate_476, certificate_476_valid⟩, ⟨⟨certificate_477, certificate_477_valid⟩, ⟨⟨certificate_478, certificate_478_valid⟩, ⟨⟨certificate_479, certificate_479_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_12_7_2_verified : ∀ D ∈ patterns_12_7_2, PatternVerified 12 7 D := by

  simp only [patterns_12_7_2, List.forall_mem_cons]

  exact ⟨⟨certificate_480, certificate_480_valid⟩, ⟨⟨certificate_481, certificate_481_valid⟩, ⟨⟨certificate_482, certificate_482_valid⟩, ⟨⟨certificate_483, certificate_483_valid⟩, ⟨⟨certificate_484, certificate_484_valid⟩, ⟨⟨certificate_485, certificate_485_valid⟩, ⟨⟨certificate_486, certificate_486_valid⟩, ⟨⟨certificate_487, certificate_487_valid⟩, ⟨⟨certificate_488, certificate_488_valid⟩, ⟨⟨certificate_489, certificate_489_valid⟩, ⟨⟨certificate_490, certificate_490_valid⟩, ⟨⟨certificate_491, certificate_491_valid⟩, ⟨⟨certificate_492, certificate_492_valid⟩, ⟨⟨certificate_493, certificate_493_valid⟩, ⟨⟨certificate_494, certificate_494_valid⟩, ⟨⟨certificate_495, certificate_495_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_12_7_3_verified : ∀ D ∈ patterns_12_7_3, PatternVerified 12 7 D := by

  simp only [patterns_12_7_3, List.forall_mem_cons]

  exact ⟨⟨certificate_496, certificate_496_valid⟩, ⟨⟨certificate_497, certificate_497_valid⟩, ⟨⟨certificate_498, certificate_498_valid⟩, (by simp)⟩⟩⟩

theorem patterns_12_7_verified : ∀ D ∈ patterns_12_7, PatternVerified 12 7 D := by

  simp only [patterns_12_7, List.forall_mem_append]

  exact ⟨patterns_12_7_0_verified, ⟨patterns_12_7_1_verified, ⟨patterns_12_7_2_verified, ⟨patterns_12_7_3_verified, by simp⟩⟩⟩⟩

theorem patterns_12_7_coverage : patternChoices 7 5 [] = patterns_12_7 := by decide +kernel

theorem finite_patterns_12_7_oai : ∀ D ∈ patternChoices 7 (12-7) [], PatternVerified 12 7 D := by

  rw [patterns_12_7_coverage]

  exact patterns_12_7_verified

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.finite_patterns_12_7_oai := @OAI.CycleClique.finite_patterns_12_7_oai
