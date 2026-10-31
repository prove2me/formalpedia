-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.rank_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:32:41.994615+00:00
-- url     : https://prove2.me/submissions/dc6f0e56-5f53-4ef6-801f-adcb319ffe07

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S176
import Definitions.Def_OAIQ081S177
import Definitions.Def_OAIQ081S178
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_BucketProgram_ProducedRank_actualMax_rank_budget
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafPackingFiberBounds_query_factor_fiber_le
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_ProducedQueryRank_packing_coverage

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Incidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite factor incidence bounds

Scopes are finite sets: a coordinate occurs at most once in any single factor,
while distinct factors may have equal scopes.  The results below count actual
incidences, bound the neighbors sharing a factor, and account for packing
Boolean variables into chunks followed by one unary validity factor per chunk.
-/

namespace SubexponentialSAT.Incidence

open scoped BigOperators

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]

omit [DecidableEq E] in
/-- Counting incidences by coordinates or by factors gives the same result. -/
theorem sum_degrees [Fintype V] (scope : E → Finset V) :
    ∑ v, degree scope v = ∑ e, (scope e).card := by
  simp_rw [degree_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp

end SubexponentialSAT.Incidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpExponentArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Growing-parameter exponent arithmetic

All factors in this module are actual real powers. The bounds expose the
growing parameters; they assert no program-running-time fact.
-/

namespace SubexponentialSAT.SubexpExponentArithmetic

noncomputable section
open Filter
open scoped Topology

theorem logb_lt_natLog2_add_one (n : ℕ) :
    Real.logb 2 (n : ℝ) < (Nat.log2 n : ℝ) + 1 := by
  have hf : ⌊Real.logb 2 (n : ℝ)⌋₊ = Nat.log2 n := by
    rw [Nat.log2_eq_log_two]
    exact Real.natFloor_logb_natCast 2 n
  simpa only [hf] using
    (Nat.lt_floor_add_one (Real.logb 2 (n : ℝ)))

end
end SubexponentialSAT.SubexpExponentArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticTarget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Conversion to the exact natural-logarithm target and absorption of
fixed polylogarithmic construction, search, and arithmetic overheads. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem log_two_bounds : (1 : ℝ) / 2 ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_AsymptoticLayoutParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer layout parameters agreed with the layout and spectral components.
The occurrence bound `b` is an explicit argument. Positivity assumptions are
kept on theorems rather than built into an opaque choice. -/

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem layoutCutoff_ge_four (n b : ℕ) : 4 ≤ layoutCutoff n b := by
  unfold layoutCutoff
  omega
theorem layoutEpsilon_pos (n : ℕ) {b : ℕ} (hb : 0 < b) : 0 < layoutEpsilon n b := by
  have hr := layoutR_ge_two n
  have hL := L_pos n
  unfold layoutEpsilon
  positivity

theorem layoutCutoff_square (n b : ℕ) :
    128 * layoutQ n * layoutEnergy n b ≤ layoutCutoff n b ^ 2 := by
  have h := Nat.lt_succ_sqrt' (128 * layoutQ n * layoutEnergy n b)
  simp only [Nat.succ_eq_add_one] at h
  unfold layoutCutoff
  exact h.le.trans (Nat.pow_le_pow_left (by omega) 2)

theorem layout_log_epsilon_le (n : ℕ) {b : ℕ} (hb : 0 < b) :
    Real.log (2 / (layoutEpsilon n b : ℝ)) ≤ layoutEnergy n b := by
  have hr : 0 < layoutR n := by have := layoutR_ge_two n; omega
  have hL := L_pos n
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hr' : (0 : ℝ) < layoutR n := by exact_mod_cast hr
  have hL' : (0 : ℝ) < L n := by exact_mod_cast hL
  have he : (layoutEpsilon n b : ℝ) = 1 / (32 * (b : ℝ) * layoutR n * (L n : ℝ) ^ 2) := by
    norm_num [layoutEpsilon]
  have hid : 2 / (layoutEpsilon n b : ℝ) = (64 * b * layoutR n * L n ^ 2 : ℕ) := by
    rw [he]
    push_cast
    field_simp
    ; ring
  rw [hid]
  have hx : 1 ≤ (64 * b * layoutR n * L n ^ 2 : ℕ) := by
    have : 0 < 64 * b * layoutR n * L n ^ 2 := by positivity
    omega
  have hx' : (1 : ℝ) ≤ (64 * b * layoutR n * L n ^ 2 : ℕ) := by exact_mod_cast hx
  have hlog := Real.log_nonneg hx'
  have htwo := log_two_bounds
  have hl : Real.log (64 * b * layoutR n * L n ^ 2 : ℕ) ≤
      Real.logb 2 (64 * b * layoutR n * L n ^ 2 : ℕ) := by
    unfold Real.logb
    apply (le_div_iff₀ (show 0 < Real.log (2 : ℝ) by linarith)).2
    nlinarith
  apply hl.trans
  have hh := (SubexpExponentArithmetic.logb_lt_natLog2_add_one
    (64 * b * layoutR n * L n ^ 2)).le
  push_cast at hh
  dsimp only [layoutEnergy]
  push_cast
  exact hh

theorem layout_spectral_square (n : ℕ) {b : ℕ} (hb : 0 < b) :
    32 * ((layoutQ n - 1 : ℕ) : ℝ) * Real.log (2 / (layoutEpsilon n b : ℝ)) ≤
      (layoutCutoff n b : ℝ) ^ 2 := by
  have hlog := layout_log_epsilon_le n hb
  have hQ : ((layoutQ n - 1 : ℕ) : ℝ) ≤ layoutQ n := by exact_mod_cast Nat.sub_le (layoutQ n) 1
  have hsq : (128 : ℝ) * layoutQ n * layoutEnergy n b ≤ (layoutCutoff n b : ℝ) ^ 2 := by
    exact_mod_cast layoutCutoff_square n b
  calc
    32 * ((layoutQ n - 1 : ℕ) : ℝ) * Real.log (2 / (layoutEpsilon n b : ℝ)) ≤
        32 * ((layoutQ n - 1 : ℕ) : ℝ) * layoutEnergy n b :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ 32 * (layoutQ n : ℝ) * layoutEnergy n b := by gcongr
    _ ≤ 128 * (layoutQ n : ℝ) * layoutEnergy n b := by gcongr ; norm_num
    _ ≤ _ := hsq

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsTotals
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed finite-sum and maximum specifications of the native variable scan. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram

theorem totals_free (scopes : List (List ℕ)) (v : ℕ) (mask : List Bool) (t : Totals) :
    (variableTotals scopes v mask t).free = t.free + scanSum (fun _ => 1) v mask := by
  induction mask generalizing v t with
  | nil => simp [variableTotals]
  | cons b bs ih =>
    cases b <;> simp [variableTotals, Totals.add, ih, Nat.add_assoc]

theorem totals_incidences (scopes : List (List ℕ)) (v : ℕ) (mask : List Bool) (t : Totals) :
    (variableTotals scopes v mask t).incidences =
      t.incidences + scanSum (fun i => max 1 (degree scopes i)) v mask := by
  induction mask generalizing v t with
  | nil => simp [variableTotals]
  | cons b bs ih =>
    cases b <;> simp [variableTotals, Totals.add, ih, Nat.add_assoc]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The runtime scan equals the statistics of the actual residual scope family,
with precisely one neutral singleton for each unused free coordinate. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram HighIncidence

theorem scanSum_eq_free_sum (f : ℕ → ℕ) (mask : List Bool) :
    scanSum f 0 mask = ∑ i : Free mask, f i.val.val := by
  unfold scanSum
  simp only [Nat.zero_add]
  calc
    _ = ∑ i ∈ (Finset.univ.filter fun i : Fin mask.length => i ∉ highMask mask), f i.val := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      simp only [mem_highMask, List.get_eq_getElem]
      by_cases hb : mask[i.val] = true <;> simp [hb]
    _ = _ := Finset.sum_subtype _ (by intro i; simp) _

theorem free_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).free = Fintype.card (Free mask) := by
  rw [totals_free, scanSum_eq_free_sum]
  simp [zero]

theorem incidences_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).incidences = totalScope (completedScope scopes mask) := by
  rw [totals_incidences, scanSum_eq_free_sum]
  simp only [zero, Nat.zero_add]
  rw [totalScope, ← Incidence.sum_degrees]
  simp only [completed_degree]

theorem occurrence_exact (scopes : List (List ℕ)) (mask : List Bool) :
    (variableTotals scopes 0 mask zero).occurrence =
      Finset.univ.sup (Incidence.degree (completedScope scopes mask)) := by
  apply Nat.le_antisymm
  · rw [totals_occurrence_le_iff]
    refine ⟨Nat.zero_le _, ?_⟩
    intro i hi
    simp only [List.get_eq_getElem] at hi
    let v : Free mask := ⟨i, by simp [hi]⟩
    simpa only [Nat.zero_add, completed_degree] using
      (Finset.le_sup (f := Incidence.degree (completedScope scopes mask)) (Finset.mem_univ v))
  · apply Finset.sup_le
    intro v _
    have h := (totals_occurrence_le_iff scopes 0 mask zero
      (variableTotals scopes 0 mask zero).occurrence).mp le_rfl
    simpa only [Nat.zero_add, completed_degree] using h.2 v.val (free_bit mask v)

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputStats
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The address stream and the native statistics use the same mask scan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Stats
open SubexponentialSAT.Subexp
open LeafStatisticsProgram

theorem native_incidence_count (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    (Loop.plans scopes n 0 scopes.length mask).length =
      (variableTotals scopes 0 mask zero).incidences := by
  rw [Semantics.plans_eq,List.length_map]
  simpa [zero] using entries_agree scopes mask 0 scopes.length zero
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Stats

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramControllerResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ordinary sizes of the actual all-row bucket input.  The row count here
is the length of the emitted incidence plan, and is never replaced by rank. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.Controller.Resources

open scoped BigOperators
open SubexponentialSAT.Subexp.MatrixProgramSupport

theorem native_rows_le (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    (PackingIncidenceInput.Loop.plans scopes n 0 scopes.length mask).length ≤
      (LeafStatisticsProgram.variableTotals scopes 0 mask LeafStatisticsSemantics.zero).free *
      (LeafStatisticsProgram.variableTotals scopes 0 mask LeafStatisticsSemantics.zero).occurrence := by
  rw [PackingIncidenceInput.Stats.native_incidence_count]
  change (LeafStatisticsProgram.variableTotals scopes 0 mask LeafStatisticsSemantics.zero).incidences ≤ _
  rw [LeafStatisticsSemantics.incidences_exact, LeafStatisticsSemantics.free_exact,
    LeafStatisticsSemantics.occurrence_exact, HighIncidence.totalScope, ← Incidence.sum_degrees]
  calc
    _ ≤ ∑ _v : LeafStatisticsSemantics.Free mask,
        Finset.univ.sup (Incidence.degree (LeafStatisticsSemantics.completedScope scopes mask)) := by
      apply Finset.sum_le_sum
      intro v _
      exact Finset.le_sup (f := Incidence.degree (LeafStatisticsSemantics.completedScope scopes mask))
        (Finset.mem_univ v)
    _ = _ := by simp

end SubexponentialSAT.SqrtLog.BucketProgram.Controller.Resources

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact runtime parameter semantics. Every definition below uses natural
arithmetic; the executable refinements are separate from these specifications.
The original ambient dimension is retained through high-incidence branching. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

theorem produce_R_ge_four (x : Input) : 4 ≤ (produce x).R := Asymptotic.layoutCutoff_ge_four _ _

theorem guard_spectral (x : Input) (h : Guard x) :
    32 * (((produce x).Q - 1 : ℕ) : ℝ) *
      Real.log (2 / (Asymptotic.layoutEpsilon x.freeCount x.occurrence : ℝ)) ≤
        ((produce x).R : ℝ) ^ 2 :=
  Asymptotic.layout_spectral_square _ h.2.2.2.1

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafPackingFiberBoundsQuery
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! No raw-fiber hypothesis is needed for a produced query: its actual scope
rows are deduplicated, and its parameter fields are the actual native scan. -/
namespace SubexponentialSAT.SqrtLog.LeafPackingFiberBounds
open PackingIncidenceInput LeafStatisticsProgram LeafQueryFrontend

 theorem query_incidences_le (q : Query) (k : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k)) :
    (LeafProgram.Query.packingProblem q k hg).incidences ≤
      (q.input k).occurrence*(q.input k).freeCount := by
  rw [LeafProgram.Query.packingProblem_incidences, Nat.mul_comm]
  have h := BucketProgram.Controller.Resources.native_rows_le q.scopeRows
    (BinaryArithmetic.toNat q.ambient) q.forward
  rw [PackingIncidenceInput.Stats.native_incidence_count] at h
  exact h

end SubexponentialSAT.SqrtLog.LeafPackingFiberBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryRankProvenance
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The rank certificate refers to the packing and word table actually
produced by the native packing caller, with its original incidence order. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram

theorem packing_head (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (i : Fin p.incidences) (t : Fin p.Q) :
    ((packing p a tail).label i).head t=words p a tail (.inl (owner p i)) t := rfl

theorem selected_head (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (low : List Bool) (t : Fin p.Q) (g : Fin p.r) (v : Fin p.n)
    (hv : v.val∈LeafHeadSetupProgram.selectedHeads p.n (rows p a tail) low (t.val*p.r+g.val)) :
    words p a tail (.inl v) t=g := by
  have hpred : HeadIdentifierProgram.predicate (rows p a tail) low (t.val*p.r+g.val) v.val=true :=
    (List.mem_filter.mp hv).2
  unfold HeadIdentifierProgram.predicate at hpred
  rw [head_row,HeadIdentifierProgram.encodeWord_getD] at hpred
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp hpred).2

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryRankSchedule
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Scheduled rank of the literal native packing. The intermediate scan
premises are discharged for produced queries in the final certificate. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram LeafParametersProgram
open BucketProgram.ProducedRank

 theorem query_rank_budget_of_scan (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (a : Word (LeafProgram.Query.packingProblem q k hg).r (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail)
    (hB : ∀ v,(Finset.univ.filter fun i => owner (LeafProgram.Query.packingProblem q k hg) i=v).card ≤
      (q.input k).occurrence)
    (hb : ∀ e,(Finset.univ.filter fun i => factor (LeafProgram.Query.packingProblem q k hg) i=e).card ≤
      (q.input k).arity)
    (hD : (LeafProgram.Query.packingProblem q k hg).incidences ≤
      (q.input k).occurrence*(q.input k).freeCount) :
    16*(Asymptotic.layoutR (q.input k).freeCount:ℝ)*(Asymptotic.L (q.input k).freeCount:ℝ)^2*
      (queryLabelRows q k hg a tail:ℝ) ≤ (q.input k).freeCount := by
  let p := LeafProgram.Query.packingProblem q k hg
  rcases hg with ⟨hm,hmn,hc,hocc,har,hmi,hQ,hRQ,hlarge,hhead⟩
  have hi : p.incidences=(q.input k).incidences := LeafProgram.Query.packingProblem_incidences q k _
  have hn : p.n=(q.input k).ambient := rfl
  have hcov := packing_coverage p a tail haN haC (q.input k).occurrence (q.input k).arity hB hb
    (by omega) (by omega)
    (by
      change 4*((q.input k).occurrence+(q.input k).arity)*
        ((produce (q.input k)).r^(2*(produce (q.input k)).Q))^2*
          (produce (q.input k)).epsilonDen^2 ≤ p.incidences
      rw [hi]
      exact hlarge)
    (by change 16*(produce (q.input k)).Q*(produce (q.input k)).r^2 ≤ p.n
        rw [hn]; exact hhead.trans hmn)
  change (1-Asymptotic.layoutEpsilon (q.input k).freeCount (q.input k).occurrence)*
    (p.incidences:ℚ) ≤ (packing p a tail).blockCount*
      (Fintype.card (UniversalType p.r p.Q 1):ℚ) at hcov
  exact actualMax_rank_budget (packing p a tail) (owner p)
    (fun t v=>words p a tail (.inl v) t) (packing_head p a tail)
    (produce (q.input k)).R (rationalDenominator (produce (q.input k)).R) rfl
    (rationalUnits p.Q) (rows p a tail) (queryLow q) Finset.univ
    (fun t _ g v hv=>selected_head p a tail (queryLow q) t g v hv)
    (q.input k).freeCount (q.input k).occurrence hocc hD
    (produce_r_ge_two _) hQ (produce_R_ge_four _) hRQ
    (Asymptotic.layoutEpsilon_pos _ hocc) (guard_spectral _ ⟨hm,hmn,hc,hocc,har,hmi,hQ,hRQ,hlarge,hhead⟩)
    hcov

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryRankCertificate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A produced query determines its actual packing and maximum selected
matrix rank. Coverage, head compatibility, node units, and raw fiber counts
are all proved from the native producer; none is a certificate premise. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram LeafParametersProgram BucketProgram.ProducedRank
open LeafHeadSetupProgram

 theorem query_rank_budget (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (a : Word (LeafProgram.Query.packingProblem q k hg).r (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    16*(Asymptotic.layoutR (q.input k).freeCount:ℝ)*(Asymptotic.L (q.input k).freeCount:ℝ)^2*
      (queryLabelRows q k hg a tail:ℝ) ≤ (q.input k).freeCount :=
  query_rank_budget_of_scan q k hg a tail haN haC
    (LeafPackingFiberBounds.query_owner_fiber_le q k hg)
    (LeafPackingFiberBounds.query_factor_fiber_le q k hg)
    (LeafPackingFiberBounds.query_incidences_le q k hg)

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryResourcesBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Simultaneous Bounds for the actual query and searched packing. Neither
rank, head size, cardinalities of bucket tables, nor running times are
assumptions of this theorem. The alphabet premises describe the output of
the native complete-alphabet enumeration. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter Asymptotic LeafQueryFrontend
open scoped Topology
open SubexponentialSAT.MulticolorTypes
noncomputable section

 theorem rank_budget_oai (q : Query) (k : ℕ) (hg : LeafParametersProgram.Guard (q.input k))
    (a : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q))
    (haN : (a::tail).Nodup) (haC : ∀z,z∈a::tail) :
    16*(layoutR (q.input k).freeCount:ℝ)*(L (q.input k).freeCount:ℝ)^2*
      (rank q k hg a tail:ℝ) ≤ (q.input k).freeCount :=
  ProducedQueryRank.query_rank_budget q k hg a tail haN haC

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.rank_budget_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.rank_budget_oai
