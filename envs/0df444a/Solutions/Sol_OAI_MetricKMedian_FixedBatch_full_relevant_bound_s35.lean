-- Prove2me | solution 1 for OAI.MetricKMedian.FixedBatch.full_relevant_bound_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T10:55:16.713804+00:00
-- url     : https://prove2.me/submissions/8709caa8-b5c3-4d5a-8b7f-95fb1e994346

import Mathlib
import Definitions.Def_OAIQ035K004

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_FixedBatchTransition
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential

variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

 theorem mem_relevant (D : Actions I E) (S : Finset I) (e : E) :
    e ∈ relevant D S ↔ (e ∈ D.ordinary ∧ D.source e ∈ S) ∨ (S ∩ D.erase e).Nonempty := by
  simp only [relevant, mem_filter, mem_univ, true_and]

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_FiniteGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteGraph

variable {I H : Type*} [Fintype H] [DecidableEq I] [DecidableEq H]

theorem mem_touching (E : H → Finset I) (S : Finset I) (h : H) :
    h ∈ touching E S ↔ ∃ i ∈ S, i ∈ E h := by
  simp only [touching, Finset.mem_biUnion, incoming, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem touching_card (E : H → Finset I) (S : Finset I) {Δ : ℕ}
    (hin : ∀ i ∈ S, (incoming E i).card ≤ Δ) :
    (touching E S).card ≤ S.card*Δ := by
  apply le_trans (Finset.card_biUnion_le) ?_
  calc
    (∑ i ∈ S, (incoming E i).card) ≤ ∑ _i ∈ S, Δ := Finset.sum_le_sum hin
    _ = S.card*Δ := by simp

end MetricKMedian.FiniteGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_ActionDegrees
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I E H : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
  [DecidableEq H] [Fintype H]

theorem relevant_card_bound (D : Actions I E) (S : Finset I) {Δ : ℕ}
    (hS : S.card ≤ Δ)
    (hsource : (D.ordinary : Set E).InjOn D.source)
    (hin : ∀ i ∈ S, (FiniteGraph.incoming D.erase i).card ≤ Δ) :
    (relevant D S).card ≤ Δ^2+Δ := by
  let U := D.ordinary.filter (fun e => D.source e ∈ S)
  have hU : U.card ≤ S.card := by
    apply card_le_card_of_injOn D.source
    · intro e he
      exact (mem_filter.mp he).2
    · intro e he f hf hef
      exact hsource (mem_filter.mp he).1 (mem_filter.mp hf).1 hef
  have heq : relevant D S=U ∪ FiniteGraph.touching D.erase S := by
    ext e
    simp only [mem_relevant, mem_union, U, mem_filter, FiniteGraph.mem_touching,
      nonempty_def, mem_inter]
  rw [heq]
  calc
    _ ≤ U.card+(FiniteGraph.touching D.erase S).card := card_union_le _ _
    _ ≤ S.card+S.card*Δ := Nat.add_le_add hU (FiniteGraph.touching_card _ _ hin)
    _ ≤ Δ+Δ*Δ := Nat.add_le_add hS (Nat.mul_le_mul_right Δ hS)
    _ = Δ^2+Δ := by ring

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_SourceGenerator
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I : Type*} [DecidableEq I] [Fintype I]

 theorem mem_graph_erase (G : I → Finset I) (h i : I) :
    i ∈ (graphActions G).erase h ↔ h ∈ G i := by simp [graphActions]

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_ActualActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential FiniteGraph
variable {I E : Type*} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

 theorem full_incoming_card (G : I → Finset I) (i : I) :
    (incoming (graphActions G).erase i).card=(G i).card := by
  congr 1
  ext h
  simp [incoming,mem_graph_erase]

 theorem full_relevant_bound_s35_oai (G : I → Finset I) (S : Finset I) {Δ : ℕ}
    (hS : S.card ≤ Δ) (hG : ∀ i, (G i).card=Δ) :
    (relevant (graphActions G) S).card ≤ Δ^2+Δ := by
  apply relevant_card_bound _ _ hS (fun _ _ _ _ h => h)
  intro i _
  exact le_of_eq ((full_incoming_card G i).trans (hG i))

end MetricKMedian.FixedBatch
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedian.FixedBatch.full_relevant_bound_s35_oai.{u_1} := @OAI.MetricKMedian.FixedBatch.full_relevant_bound_s35_oai.{u_1}
