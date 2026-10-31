-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.query_max_bound_rat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:43:24.250208+00:00
-- url     : https://prove2.me/submissions/73f37614-2f8a-4acc-be90-08b03b9023dd

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S176
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProducedHeads_problem_head_max_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafPackingFiberBounds_query_factor_fiber_le

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProducedHeadsQuery
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The maximum size of an actually emitted head list is bounded directly
from a query's integer guards. Ambient owner IDs remain unchanged, while
all layout parameters use the measured free-variable count. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProducedHeads
open SubexponentialSAT.MulticolorTypes LeafParametersProgram LeafQueryFrontend

 theorem query_low_bytes (q : Query) (k : ℕ) (hg : Guard (q.input k)) :
    q.forward.map Bool.not = HeadIdentifierProgram.lowBits
      (fun v : Fin (LeafProgram.Query.packingProblem q k hg).n =>
        !(q.forward.getD v.val false)) := by
  have hl : q.forward.length=(LeafProgram.Query.packingProblem q k hg).n := by
    simp [Query.forward,highMask,LeafProgram.Query.packingProblem]
  apply List.ext_getElem
  · simp [HeadIdentifierProgram.lowBits,hl]
  · intro i hi hj
    have hi' : i < q.forward.length := by simpa only [List.length_map] using hi
    simp [HeadIdentifierProgram.lowBits,List.getElem?_eq_getElem hi']

/-- This is the actual finite maximum over all node/head addresses, not an
assumed head-size parameter. No validity premise beyond the checked integer
guards is needed for these structurally deduplicated query scopes. -/
 theorem query_max_bound_rat_oai (q : Query) (k : ℕ) (hg : Guard (q.input k))
    (a : Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    let p := LeafProgram.Query.packingProblem q k hg
    (maxSelected p.n p.Q p.r ((p.words a tail).map SubexponentialSAT.Subexp.ReadPlan.encodeWord)
      (q.forward.map Bool.not) : ℚ) ≤ 3*(p.n:ℚ)/(2*(p.r:ℚ)) := by
  let p := LeafProgram.Query.packingProblem q k hg
  have hg' := hg
  change (maxSelected p.n p.Q p.r ((p.words a tail).map _)
    (q.forward.map Bool.not) : ℚ) ≤ _
  rw [query_low_bytes q k hg]
  rcases hg with ⟨hm,hmn,hc,hocc,har,hmi,hQ,hRQ,hlarge,hhead⟩
  have hi : p.incidences=(q.input k).incidences :=
    LeafProgram.Query.packingProblem_incidences q k hg'
  have hn : p.n=(q.input k).ambient := rfl
  apply problem_head_max_bound p a tail haN haC (q.input k).occurrence (q.input k).arity
  · exact LeafPackingFiberBounds.query_owner_fiber_le q k hg'
  · exact LeafPackingFiberBounds.query_factor_fiber_le q k hg'
  · omega
  · omega
  · change 4*((q.input k).occurrence+(q.input k).arity)*
      ((produce (q.input k)).r^(2*(produce (q.input k)).Q))^2*
        (produce (q.input k)).epsilonDen^2 ≤ p.incidences
    rw [hi]
    exact hlarge
  · change 16*(produce (q.input k)).Q*(produce (q.input k)).r^2 ≤ p.n
    rw [hn]
    exact hhead.trans hmn

end SubexponentialSAT.SqrtLog.LayoutProducedHeads

end

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.query_max_bound_rat_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.query_max_bound_rat_oai
