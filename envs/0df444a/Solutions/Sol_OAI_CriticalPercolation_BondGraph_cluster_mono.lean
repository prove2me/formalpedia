-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.cluster_mono
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:14:50.459201+00:00
-- url     : https://prove2.me/submissions/64104827-da08-4d1c-a69e-f4fe3bdea421

import Mathlib
import Definitions.Def_CriticalPercolation

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_VertexBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem openGraph_mono {ω ω' : Set E} (h : ω ⊆ ω') :
    G.openGraph ω ≤ G.openGraph ω' :=
  SimpleGraph.fromEdgeSet_mono (Set.image_mono h)

theorem cluster_mono_oai {ω ω' : Set E} (h : ω ⊆ ω') (v : V) :
    G.cluster ω v ⊆ G.cluster ω' v :=
  fun _ hw => hw.mono (G.openGraph_mono h)

end BondGraph

end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.cluster_mono_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.cluster_mono_oai.{u_1, u_2}
