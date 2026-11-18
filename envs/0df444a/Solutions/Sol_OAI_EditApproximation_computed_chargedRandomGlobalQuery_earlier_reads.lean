-- Prove2me | solution 1 for OAI.EditApproximation.computed_chargedRandomGlobalQuery_earlier_reads
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:34:37.207371+00:00
-- url     : https://prove2.me/submissions/af4917d0-fa42-4adf-9fe5-fc56b9f62408

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Int.Log
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_OAIQ361V3Ea002
import Definitions.Def_OAIQ361V3Ea003
import Theorems.Thm_OAI_EditApproximation_computed_localRandomDataQuery_table_cost

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer-computed parameters

The logarithms and fourth roots in Section 2 are computed by natural bit
lengths and nested integer square roots. No real arithmetic oracle is
used to form the algorithm's parameters.
-/

namespace EditApproximation
















theorem inputSmallLog_bounds (N : ℕ) (hN : 0 < N) :
    heightExponent N ≤ inputSmallLog N ∧ inputSmallLog N < 2 * heightExponent N := by
  have hpos := heightExponent_pos N hN
  have hone : 1 ≤ heightExponent N := hpos
  have hrange := rejectionWord_range (heightExponent N) hpos
  simpa only [inputSmallLog, smallLogExponent, rejectionBitCount, max_eq_right hone] using hrange

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_LocalGrid
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Direct enumeration of a local grid square

The algorithm enumerates bounded ranges of grid indices. It does not
scan the unrelated target positions. The completeness theorem includes
boundary states and intervals with equal endpoints.
-/

namespace EditApproximation



theorem localTargetStates_length_le {n g radius : ℕ} (hg : 0 < g)
    (q : TargetInterval n) :
    (localTargetStates n g radius q).length ≤ (2 * radius / g + 2) ^ 2 := by
  have hpoint (p : ℕ) :
      (gridPointsBetween g (p - radius) (p + radius)).length ≤ 2 * radius / g + 2 := by
    have hlength := gridPointsBetween_length_le g (p - radius) (p + radius) hg
    have hwidth : p + radius - (p - radius) ≤ 2 * radius := by omega
    exact hlength.trans (Nat.add_le_add_right (Nat.div_le_div_right hwidth) 2)
  have hlist := list_flatMap_length_le
    (gridPointsBetween g (q.lo - radius) (q.lo + radius))
    (fun lo => (gridPointsBetween g (q.hi - radius) (q.hi + radius)).filterMap
      fun hi => makeTargetState n lo hi)
    (2 * radius / g + 2) (by
      intro lo hlo
      exact (List.length_filterMap_le _ _).trans (hpoint q.hi))
  exact hlist.trans (by simpa only [pow_two] using
    (Nat.mul_le_mul_right (2 * radius / g + 2) (hpoint q.lo)))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DyadicQueryWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The query scale window has length controlled by the refinement
factor, independently of the number of dyadic scales below N. -/

namespace EditApproximation

open Finset



theorem dyadicQueryWindow_length_le (N C : ℕ) (w a F : ℚ)
    (ha : 1 ≤ a) (hF : 1 ≤ F)
    (hbudget : 128 * a * F ≤ (2 : ℚ) ^ C) :
    (dyadicQueryWindow N w a F).length ≤ C + 1 := by
  let keep : ℕ → Bool := fun e => decide (w / (16 * F) ≤ (2 ^ e : ℕ) ∧
    ((2 ^ e : ℕ) : ℚ) ≤ 8 * a * w)
  let indices := ((List.range (Nat.log 2 N + 1)).filter keep).toFinset
  have hlength : (dyadicQueryWindow N w a F).length = indices.card := by
    simp only [dyadicQueryWindow, dyadicScales, List.filter_map, List.length_map]
    exact (List.toFinset_card_of_nodup
      ((show (List.range (Nat.log 2 N + 1)).Nodup from List.nodup_range).filter keep)).symm
  rw [hlength]
  by_cases hnonempty : indices.Nonempty
  · let first := indices.min' hnonempty
    have hfirst : first ∈ indices := Finset.min'_mem _ _
    have hfirstKeep : w / (16 * F) ≤ (2 ^ first : ℕ) ∧ ((2 ^ first : ℕ) : ℚ) ≤ 8 * a * w :=
      of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hfirst)).2
    have hFpos : 0 < F := lt_of_lt_of_le zero_lt_one hF
    have hwfirst : w ≤ 16 * F * (2 ^ first : ℕ) := by
      nlinarith only [(div_le_iff₀ (by positivity : (0 : ℚ) < 16 * F)).mp hfirstKeep.1]
    have hsub : indices ⊆ Finset.Icc first (first + C) := by
      intro e he
      have hkeep : w / (16 * F) ≤ (2 ^ e : ℕ) ∧ ((2 ^ e : ℕ) : ℚ) ≤ 8 * a * w :=
        of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp he)).2
      have hmul := mul_le_mul_of_nonneg_left hwfirst (show 0 ≤ 8 * a by positivity)
      have hpower := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg (α := ℚ) (2 ^ first))
      have hbound : ((2 ^ e : ℕ) : ℚ) ≤ (2 : ℚ) ^ C * (2 ^ first : ℕ) := by
        nlinarith only [hkeep.2, hmul, hpower]
      have hboundN : 2 ^ e ≤ 2 ^ (first + C) := by
        have heq : (2 : ℚ) ^ C * (2 ^ first : ℕ) = ((2 ^ (first + C) : ℕ) : ℚ) := by
          push_cast
          rw [pow_add]
          ring
        rw [heq] at hbound
        exact_mod_cast hbound
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ he,
        (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hboundN⟩
    have hcard := Finset.card_le_card hsub
    have hinterval : (Finset.Icc first (first + C)).card = C + 1 := by rw [Nat.card_Icc]; omega
    rwa [hinterval] at hcard
  · simpa only [Finset.not_nonempty_iff_eq_empty.mp hnonempty, Finset.card_empty] using Nat.zero_le (C + 1)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SeedFactorSchedule
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The literal dyadic factor schedule stops at A<=F. Each active pass
replaces A by 4A/F and uses the integer factor a=A/F. -/

namespace EditApproximation





theorem computedSeed_initial_factor (N : ℕ) :
    (2 : ℚ) ^ computedSeedInitialExponent N =
      ((integerParameters N).initialFactor : ℚ) := by
  simp only [computedSeedInitialExponent, integerParameters, inputHeight, Nat.cast_pow, Nat.cast_ofNat]
  rw [← pow_mul, Nat.mul_comm]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalQueryBudget
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal online loop is bounded by the applicable scale window,
which is polynomial in ell throughout the computed factor schedule. -/

namespace EditApproximation

open Finset

theorem refinement_query_window_length (N F initialExponent : ℕ) (A w : ℚ)
    (hF : 1 ≤ F) (hFbound : (F : ℚ) ≤ (2 : ℚ) ^ initialExponent)
    (hAbound : A ≤ (2 : ℚ) ^ initialExponent) :
    (dyadicQueryWindow N w (refinementFactor A F) F).length ≤ initialExponent + 8 := by
  have hFpos : (0 : ℚ) < F := by exact_mod_cast (by omega : 0 < F)
  have hfactor : refinementFactor A F ≤ (2 : ℚ) ^ initialExponent / F := by
    apply max_le
    · exact (le_div_iff₀ hFpos).2 (by simpa only [one_mul] using hFbound)
    · exact div_le_div_of_nonneg_right hAbound hFpos.le
  have hproduct := mul_le_mul_of_nonneg_right hfactor hFpos.le
  rw [div_mul_cancel₀ _ hFpos.ne'] at hproduct
  have hbudget : 128 * refinementFactor A F * F ≤ (2 : ℚ) ^ (initialExponent + 7) := by
    have h := mul_le_mul_of_nonneg_left hproduct (by norm_num : (0 : ℚ) ≤ 128)
    rw [pow_add]
    norm_num only [show (2 : ℚ) ^ 7 = 128 by norm_num]
    nlinarith only [h]
  simpa only [Nat.add_assoc, show (7 : ℕ) + 1 = 8 by rfl] using
    dyadicQueryWindow_length_le N (initialExponent + 7) w (refinementFactor A F) F
      (le_max_left _ _) (by exact_mod_cast hF) hbudget

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Counts of the actual persistent interpreter. Dictionary operations
are charged on every request, including hits; insertion and retained-node
costs are charged only when a value is computed. -/

namespace EditApproximation

namespace FiniteQuery

theorem cost_eq_sum {ι : Type*} (oracle : ι → ℚ) (weight : ι → ℕ)
    (program : FiniteQuery ι) :
    program.cost oracle weight = ((program.keys oracle).map weight).sum := by
  induction program with
  | done _ => rfl
  | read key next ih => exact congrArg (weight key + ·) (ih (oracle key))

end FiniteQuery

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteQueryWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact read costs for the finite query combinators used in warmup
and refinement. In particular, a collected value is computed once and
is reused by the continuation's local arithmetic. -/

namespace EditApproximation.FiniteQuery

theorem cost_bind {ι : Type*} (oracle : ι → ℚ) (weight : ι → ℕ)
    (program : FiniteQuery ι) (next : ℚ → FiniteQuery ι) :
    (bind program next).cost oracle weight = program.cost oracle weight +
      (next (program.value oracle)).cost oracle weight := by
  induction program with
  | done result => simp only [bind, cost, value, Nat.zero_add]
  | read key continuation ih =>
    simp only [bind, cost, value, ih, Nat.add_assoc]

theorem cost_collect {ι κ : Type*} (oracle : ι → ℚ) (weight : ι → ℕ)
    (reader : κ → FiniteQuery ι) (keys : List κ) (next : List ℚ → FiniteQuery ι) :
    (collect reader keys next).cost oracle weight =
      (keys.map fun key => (reader key).cost oracle weight).sum +
      (next (keys.map fun key => (reader key).value oracle)).cost oracle weight := by
  induction keys generalizing next with
  | nil => simp only [collect, List.map_nil, List.sum_nil, Nat.zero_add]
  | cons key keys ih =>
    simp only [collect, cost_bind, ih, List.map_cons, List.sum_cons, Nat.add_assoc]

end EditApproximation.FiniteQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedSeedQuery
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A pass-zero seed read requests a cached coarse entry. Later seed reads
request the previous pass's final table value in each distinct copy.
Thus neither kind of seed value enters the charged program as a free oracle. -/

namespace EditApproximation







theorem chargedSeedQuery_cost {M J ny passes copies T S : ℕ} (N : ℕ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J ny // r.Bounded passes copies T S})
    (state : PhysicalEntry M J ny)
    (oracle : {child : ChargedPhysicalRequest M J ny passes copies T S //
      child.rank < ChargedPhysicalRequest.rank (Sum.inr parent)} → ℚ) :
    (chargedSeedQuery N multiplier parent state).cost oracle (fun _ => 1) =
      if state.1 = parent.val.node then if parent.val.pass = 0 then 1 else copies else 0 := by
  unfold chargedSeedQuery
  split_ifs with hnode hpass
  · rfl
  · rw [FiniteQuery.cost_collect]
    simp only [chargedPreviousRead, FiniteQuery.cost, Nat.add_zero, List.map_const',
      List.length_finRange, List.sum_replicate, smul_eq_mul, Nat.mul_one]
  · rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteQueryRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Restriction of adaptive read programs to a proved finite request domain.
The restriction visits the same reads whenever the original execution stays
in that domain. It does not enumerate the domain. -/

namespace EditApproximation.FiniteQuery



 theorem mapKeys_cost {ι κ : Type*} (f : ι → κ) (oracle : κ → ℚ) (weight : κ → ℕ)
    (program : FiniteQuery ι) :
    (mapKeys f program).cost oracle weight = program.cost (oracle ∘ f) (weight ∘ f) := by
  induction program with
  | done result => rfl
  | read key next ih => exact congrArg (fun rest => weight (f key) + rest) (ih (oracle (f key)))

 theorem restrict_cost {ι : Type*} (P : ι → Prop) [DecidablePred P]
    (oracle : ι → ℚ) (weight : ι → ℕ) (program : FiniteQuery ι)
    (hvalid : ∀ key ∈ program.keys oracle, P key) :
    (restrict P program).cost (fun key => oracle key.val) (fun key => weight key.val) =
      program.cost oracle weight := by
  induction program with
  | done result => rfl
  | read key next ih =>
    have hk : P key := hvalid key (by simp only [keys, List.mem_cons, true_or])
    have hnext : ∀ other ∈ (next (oracle key)).keys oracle, P other := by
      intro other hother
      exact hvalid other (List.mem_cons_of_mem key hother)
    simpa only [restrict, dite_eq_left hk, cost] using
      congrArg (fun rest => weight key + rest) (ih (oracle key) hnext)

end EditApproximation.FiniteQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_WideEarlierInputs
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Wide enumeration gathers child states before scoring its Cartesian
action list. Its recursive input count depends on the coordinate lists,
rather than the exponentially larger number of complete actions. -/

namespace EditApproximation

open Finset

theorem wideEarlierChildStateList_length_le {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (hP : 0 < P) (i : Fin M) :
    (wideChildStateList parent r b P i).length ≤ (40 * P + 2) ^ 2 := by
  have hlocal := gridStateBox_length_le ny (seedGridSpacing b P) (10 * b)
    (r.lo + ((sourceChild parent i).lo - parent.lo))
    (r.lo + ((sourceChild parent i).hi - parent.lo))
    (by unfold seedGridSpacing; omega)
  apply hlocal.trans
  apply Nat.pow_le_pow_left
  simpa only [show 2 * (10 * b) = 20 * b by omega] using seedGridSpacing_radius_count b P hP



theorem localRefinementRepresentatives_length {n : ℕ} (N P F : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) (hP : 0 < P) (hF : 1 ≤ F) :
    (localRefinementRepresentatives N P F a initial q).length ≤
      (dyadicQueryWindow N (initial q) a F).length * (64 * F * P + 2) ^ 2 := by
  unfold localRefinementRepresentatives
  apply list_flatMap_length_le
  intro b hb
  have hwindow := of_decide_eq_true (List.mem_filter.mp hb).2
  have hceil : ⌈initial q⌉₊ ≤ 16 * F * b := by
    apply Nat.ceil_le.mpr
    have hFpos : (0 : ℚ) < F := Nat.cast_pos.mpr (by omega)
    have h := (div_le_iff₀ (by positivity : (0 : ℚ) < 16 * F)).mp hwindow.1
    push_cast
    nlinarith only [h]
  have hg : 0 < seedGridSpacing b P := by unfold seedGridSpacing; omega
  have hcover : b ≤ 2 * P * seedGridSpacing b P := by
    have hquot : b / P ≤ seedGridSpacing b P := le_max_right _ _
    have hdiv := Nat.lt_mul_div_succ b hP
    nlinarith only [hquot, hdiv, hg]
  have hcount : 2 * ⌈initial q⌉₊ / seedGridSpacing b P + 2 ≤ 64 * F * P + 2 := by
    have hprod : 2 * ⌈initial q⌉₊ ≤ 64 * F * P * seedGridSpacing b P := by
      nlinarith only [hceil, Nat.mul_le_mul_left (32 * F) hcover]
    have hdiv := Nat.div_mul_le_self (2 * ⌈initial q⌉₊) (seedGridSpacing b P)
    have hquot : 2 * ⌈initial q⌉₊ / seedGridSpacing b P ≤ 64 * F * P := by
      nlinarith only [hprod, hdiv, hg]
    exact Nat.add_le_add_right hquot 2
  have hlocal := localTargetStates_length_le (radius := ⌈initial q⌉₊) hg q
  simpa only [List.length_map] using
    (List.length_filter_le _ _).trans (hlocal.trans (Nat.pow_le_pow_left hcount 2))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RefinementDataQueryWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Read counts for the full adaptive data query. Weighting reads permits
the same theorem to count current-index and earlier-index dependencies
separately. The bounds count executed readers, including repeated reads
across successive gathering stages. -/

namespace EditApproximation

theorem list_map_sum_le_constant {ι : Type*} (inputs : List ι) (cost : ι → ℕ) (bound : ℕ)
    (hcost : ∀ input, cost input ≤ bound) :
    (inputs.map cost).sum ≤ inputs.length * bound := by
  calc
    _ ≤ (inputs.map fun _ => bound).sum := List.sum_le_sum (fun input _ => hcost input)
    _ = _ := by simp

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRefinementReadWork
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Split the literal recursive reads by the unified table index. The
current-index reads are physical-child requests; initial data, warmup
mass and old history have strictly smaller indices. -/

namespace EditApproximation

theorem physicalRefinementWarmupRead_cost_earlier {M J ny : ℕ} (pass copy T S t : ℕ)
    (ht : 0 < t) (node : PhysicalNode M J) (q : TargetInterval ny)
    (otherNode : PhysicalNode M J) (hnode : node.1.val ≤ otherNode.1.val)
    (j : ℕ) (hj : j ≤ T) (r : TargetInterval ny) (oracle) :
    (physicalRefinementWarmupRead pass copy T S t ht node q otherNode hnode j hj r).cost
      oracle (fun request => physicalEarlierReadWeight (T + t) request.val) = 1 := by
  have hlt : j < T + t := by omega
  simp only [physicalRefinementWarmupRead, FiniteQuery.cost, physicalEarlierReadWeight,
    PhysicalTableRequest.warmup, ite_eq_left hlt, Nat.add_zero]

theorem physicalRefinementMassQuery_cost_earlier {M J ny : ℕ} (pass copy T S t : ℕ)
    (ht : 0 < t) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (q : TargetInterval ny) (input : Fin M × TargetInterval ny) (oracle) :
    (physicalRefinementMassQuery pass copy T S t ht node hbelow q input).cost
      oracle (fun request => physicalEarlierReadWeight (T + t) request.val) = T := by
  simp only [physicalRefinementMassQuery, FiniteQuery.cost_collect, FiniteQuery.cost,
    physicalRefinementWarmupRead_cost_earlier, List.map_ofFn, Function.comp_def,
    List.sum_ofFn, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, Nat.mul_one, Nat.add_zero]

theorem physicalRefinementCurrentQuery_cost_earlier {M J ny : ℕ} (pass copy T S t : ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval ny)
    (input : Fin M × TargetInterval ny) (oracle) :
    (physicalRefinementCurrentQuery pass copy T S t node hbelow q input).cost
      oracle (fun request => physicalEarlierReadWeight (T + t) request.val) = 0 := by
  simp only [physicalRefinementCurrentQuery, FiniteQuery.cost, physicalEarlierReadWeight,
    PhysicalTableRequest.refinement, lt_self_iff_false, ite_false, if_false, Nat.add_zero]

theorem physicalRefinementEarlierQuery_cost_earlier {M J ny : ℕ} (pass copy T S t : ℕ)
    (node : PhysicalNode M J) (hbelow : node.1.val < J) (q : TargetInterval ny)
    (input : Fin M × ℕ × TargetInterval ny) (oracle) :
    (physicalRefinementEarlierQuery pass copy T S t node hbelow q input).cost
      oracle (fun request => physicalEarlierReadWeight (T + t) request.val) ≤ 1 := by
  unfold physicalRefinementEarlierQuery
  split_ifs with hs
  · have hlt : T + input.2.1 < T + t := by omega
    simp only [FiniteQuery.cost, physicalEarlierReadWeight, PhysicalTableRequest.refinement,
      hlt, ↓reduceIte, Nat.add_zero, le_refl]
  · exact Nat.zero_le 1

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalQueryProgress
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dependency split for keys actually emitted by the adaptive local
queries. Current-index edges descend in the physical tree; older reads
decrease the table rank and never move to an ancestor. -/

namespace EditApproximation

namespace PhysicalTableRequest

theorem rank_lt_iff_index_lt_of_pass {M J ny : ℕ} (T S : ℕ)
    (parent child : PhysicalTableRequest M J ny) (hpass : child.pass = parent.pass) :
    child.rank T S < parent.rank T S ↔ child.index < parent.index := by
  unfold rank
  rw [hpass]
  omega

end PhysicalTableRequest

theorem physicalRefinementWarmupRead_keys_pass_copy {M J ny : ℕ}
    (pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (q : TargetInterval ny)
    (otherNode : PhysicalNode M J) (hnode : node.1.val ≤ otherNode.1.val)
    (j : ℕ) (hj : j ≤ T) (r : TargetInterval ny) (oracle) :
    ∀ key ∈ (physicalRefinementWarmupRead pass copy T S t ht node q otherNode hnode j hj r).keys oracle,
      key.val.pass = pass ∧ key.val.copy = copy ∧ key.val.index ≤ T + t := by
  intro key hk
  simp only [physicalRefinementWarmupRead, FiniteQuery.keys, List.mem_singleton] at hk
  subst key
  exact ⟨rfl, rfl, hj.trans (Nat.le_add_right T t)⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_GlobalQueryCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact weighted-cost transport for the full internal refinement body.
In this branch every request is an ordinary table request: parent initial,
child mass, child initial, old history or a current physical child. -/

namespace EditApproximation

namespace FiniteQuery

theorem cost_congr_weights {ι : Type*} (oracle : ι → ℚ) (program : FiniteQuery ι)
    (left right : ι → ℕ) (heq : ∀ key ∈ program.keys oracle, left key = right key) :
    program.cost oracle left = program.cost oracle right := by
  rw [cost_eq_sum, cost_eq_sum]
  congr 1
  exact List.map_congr_left heq

end FiniteQuery

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedIndexCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The charged request index distinguishes previous passes and coarse
leaves. For internal refinement its two index classes are exactly the
current and earlier table-read counters. -/

namespace EditApproximation

theorem chargedEarlierWeight_table {M J ny passes copies T S : ℕ}
    (parent : {r : PhysicalTableRequest M J ny // r.Bounded passes copies T S}) :
    chargedEarlierWeight (Sum.inr parent) = chargedTableWeight 1
      (fun child => if child.rank T S < parent.val.rank T S then 1 else 0) := by
  funext child
  cases child <;> simp only [chargedEarlierWeight, ChargedPhysicalRequest.index, chargedTableWeight,
    Nat.zero_lt_succ, ite_true, if_true, Nat.add_lt_add_iff_right]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourceRankedRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Restrict only the recursive table keys of a mixed source/table query.
The source reads remain explicit. This preserves the finite cache domain
without materializing any counterfactual table. -/

namespace EditApproximation.SourceRanked

variable {σ κ : Type*} (tableRank : κ → ℕ) (supported : κ → Prop)







 theorem restrictBody_cost
    (tableBody : (parent : κ) → FiniteQuery (Sum σ {key : κ // tableRank key < tableRank parent}))
    (sourceValue : σ → ℚ) (tableValue : κ → ℚ) (sourceWeight : σ → ℕ) (tableWeight : κ → ℕ)
    (parent : {key : κ // supported key})
    (hkeys : ∀ key ∈ (tableBody parent.val).keys (Sum.elim sourceValue (fun key => tableValue key.val)),
      supportedChild tableRank supported parent.val key) :
    (restrictBody tableRank supported tableBody parent).cost
        (Sum.elim sourceValue (fun key => tableValue key.val.val))
        (Sum.elim sourceWeight (fun key => tableWeight key.val.val)) =
      (tableBody parent.val).cost (Sum.elim sourceValue (fun key => tableValue key.val))
        (Sum.elim sourceWeight (fun key => tableWeight key.val)) := by
  classical
  unfold restrictBody
  rw [FiniteQuery.mapKeys_cost]
  have horacle :
      (Sum.elim sourceValue (fun key => tableValue key.val.val)) ∘
        supportedChildMap tableRank supported parent =
      (fun key => (Sum.elim sourceValue (fun key => tableValue key.val)) key.val) := by
    funext key
    rcases key with ⟨key, hs⟩
    cases key <;> rfl
  have hweight :
      (Sum.elim sourceWeight (fun key => tableWeight key.val.val)) ∘
        supportedChildMap tableRank supported parent =
      (fun key => (Sum.elim sourceWeight (fun key => tableWeight key.val)) key.val) := by
    funext key
    rcases key with ⟨key, hs⟩
    cases key <;> rfl
  rw [horacle, hweight]
  exact FiniteQuery.restrict_cost _ _ _ _ hkeys

end EditApproximation.SourceRanked

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRandomBoundedCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Bounded

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (sourceValue : σ → ℚ) (tableValue : PhysicalTableRequest M J target.length → ℚ)

 theorem physicalRandomBoundedQuery_cost (sourceWeight : σ → ℕ)
    (tableWeight : PhysicalTableRequest M J target.length → ℕ)
    (request : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).cost
      (Sum.elim sourceValue (fun child => tableValue child.val.val))
      (Sum.elim sourceWeight (fun child => tableWeight child.val.val)) =
    (physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request.val).cost
      (Sum.elim sourceValue (fun child => tableValue child.val))
      (Sum.elim sourceWeight (fun child => tableWeight child.val)) := by
  unfold physicalRandomBoundedQuery
  exact SourceRanked.restrictBody_cost _ _ _ _ _ _ _ request
    (physicalRandomGlobalQuery_keys_bounded source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta readGroup readInteger initial request.val request.property _)

end Bounded

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRandomPassCopy
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every recursive table read of an adaptive random query stays in the same
pass and copy and has no larger local index. -/

namespace EditApproximation

 theorem physicalRandomDataRequest_keys_pass_copy {σ α : Type*} (source target : List α)
    {M J : ℕ} [NeZero M] (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
    (pass copy T S t : ℕ) (ht : 0 < t)
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (readGroup : GroupScalarKey M F Q → FiniteQuery σ)
    (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
    (q : TargetInterval target.length) (oracle) :
    ∀ key ∈ (physicalRandomDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow readGroup readInteger q).keys oracle,
      match key with
      | .inl _ => True
      | .inr table => table.val.pass = pass ∧ table.val.copy = copy ∧ table.val.index ≤ T + t := by
  unfold physicalRandomDataRequestQuery
  apply localRandomDataQuery_keys_all
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key _
    trivial
  · intro input range
    apply FiniteQuery.keys_all_mapKeys
    intro key _
    trivial
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    unfold physicalRefinementEarlierQuery at hk
    split_ifs at hk with hs
    · simp only [FiniteQuery.keys, List.mem_singleton] at hk
      subst key
      exact ⟨rfl, rfl, by change T + input.2.1 ≤ T + t; omega⟩
    · exact False.elim (List.not_mem_nil hk)
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    simp only [physicalRefinementCurrentQuery, FiniteQuery.keys, List.mem_singleton] at hk
    subst key
    exact ⟨rfl, rfl, le_rfl⟩
  · intro r
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    exact physicalRefinementWarmupRead_keys_pass_copy pass copy T S t ht node q node le_rfl
      0 (Nat.zero_le T) r _ key hk
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    unfold physicalRefinementMassQuery
    apply FiniteQuery.keys_all_collect
    · intro j _ key hk
      exact physicalRefinementWarmupRead_keys_pass_copy pass copy T S t ht node q
        (physicalChild node hbelow input.1) _ j.val (Nat.le_of_lt j.isLt) input.2 _ key hk
    · intro values key hk
      exact False.elim (List.not_mem_nil hk)
  · intro input
    apply FiniteQuery.keys_all_mapKeys
    intro key hk
    exact physicalRefinementWarmupRead_keys_pass_copy pass copy T S t ht node q
      (physicalChild node hbelow input.1) _ 0 (Nat.zero_le T) input.2 _ key hk

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRandomRankCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! For a fixed pass, the physical rank partition equals the concrete
warmup/refinement index partition on every emitted data-query key. -/

namespace EditApproximation

section Costs

variable {σ α : Type*} (source target : List α) {M J : ℕ} [NeZero M]
  (N P F exponent H Q : ℕ) (tau a eta kappa delta : ℚ)
  (pass copy T S t : ℕ) (ht : 0 < t) (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (readGroup : GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)
  (q : TargetInterval target.length) (answer : PhysicalTableRequest M J target.length → ℚ)

theorem physicalRandomDataRequest_earlier_rank_cost :
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow readGroup readInteger q).cost (Sum.elim sourceAnswer (fun child => answer child.val))
      (Sum.elim (fun _ => 0) (fun child => if child.val.rank T S <
        (PhysicalTableRequest.refinement pass copy node T t q).rank T S then 1 else 0)) =
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau a eta kappa delta
      pass copy T S t ht node hbelow readGroup readInteger q).cost (Sum.elim sourceAnswer (fun child => answer child.val))
      (Sum.elim (fun _ => 0) (fun child => physicalEarlierReadWeight (T + t) child.val)) := by
  apply FiniteQuery.cost_congr_weights
  intro key hk
  have hkey := physicalRandomDataRequest_keys_pass_copy source target N P F exponent H Q
    tau a eta kappa delta pass copy T S t ht node hbelow readGroup readInteger q _ key hk
  cases key with
  | inl key => rfl
  | inr key =>
    simp only [Sum.elim_inr]
    have heq := PhysicalTableRequest.rank_lt_iff_index_lt_of_pass T S
      (PhysicalTableRequest.refinement pass copy node T t q) key.val hkey.1
    by_cases hi : key.val.index < T + t
    · have hr := heq.mpr hi
      simp only [ite_eq_left hr, physicalEarlierReadWeight, ite_eq_left hi]
    · have hr : ¬ key.val.rank T S <
          (PhysicalTableRequest.refinement pass copy node T t q).rank T S := fun h => hi (heq.mp h)
      simp only [ite_eq_right hr, physicalEarlierReadWeight, ite_eq_right hi]

end Costs

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRandomCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Cost

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (sourceAnswer : σ → ℚ) (answer : PhysicalTableRequest M J target.length → ℚ)
  (sourceWeight : σ → ℕ) (coarse : ℕ) (weight : PhysicalTableRequest M J target.length → ℕ)

 theorem physicalRandomGlobalQuery_refinement_cost
    (request : PhysicalTableRequest M J target.length)
    (hindex : T < request.index) (hbelow : request.node.1.val < J)
    (hshort : ¬ (physicalSourceInterval source.length request.node).hi -
      (physicalSourceInterval source.length request.node).lo ≤ 1) :
    (physicalRandomGlobalQuery source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).cost
      (Sum.elim sourceAnswer (fun child => answer child.val))
      (Sum.elim sourceWeight (fun child => weight child.val)) =
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor request.pass) F) eta kappa delta request.pass request.copy T S
      (request.index - T) (Nat.sub_pos_of_lt hindex) request.node hbelow
      (readGroup request.pass request.copy ⟨request.node, hbelow⟩ (Fin.ofNat R (request.index - T - 1)))
      (readInteger request.pass request.copy ⟨request.node, hbelow⟩ (Fin.ofNat R (request.index - T - 1)))
      request.state).cost (Sum.elim sourceAnswer (fun child => answer child.val))
        (Sum.elim sourceWeight (fun child => weight child.val)) := by
  unfold physicalRandomGlobalQuery
  rw [dite_eq_left ⟨hindex, hbelow, hshort⟩, FiniteQuery.mapKeys_cost]
  congr 1 <;> (funext key; cases key <;> rfl)

 theorem chargedRandomGlobalQuery_refinement_cost
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)
    (hshort : ¬ (physicalSourceInterval source.length parent.val.node).hi -
      (physicalSourceInterval source.length parent.val.node).lo ≤ 1) :
    (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial (Sum.inr parent)).cost
      (Sum.elim sourceAnswer (fun child => Sum.elim (fun entry => (initial entry : ℚ))
        (fun r => answer r.val) child.val))
      (Sum.elim sourceWeight (fun child => chargedTableWeight coarse weight child.val)) =
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor parent.val.pass) F) eta kappa delta parent.val.pass parent.val.copy T S
      (parent.val.index - T) (Nat.sub_pos_of_lt hindex) parent.val.node hbelow
      (readGroup parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩
        (Fin.ofNat R (parent.val.index - T - 1)))
      (readInteger parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩
        (Fin.ofNat R (parent.val.index - T - 1))) parent.val.state).cost
      (Sum.elim sourceAnswer (fun child => answer child.val))
      (Sum.elim sourceWeight (fun child => weight child.val)) := by
  unfold chargedRandomGlobalQuery
  dsimp only
  rw [ite_eq_right (Nat.not_le.mpr hindex), ite_eq_left hbelow, ite_eq_right hshort, FiniteQuery.mapKeys_cost]
  have hcost := physicalRandomBoundedQuery_cost source target N P F exponent H Q T S passes copies
    factor multiplier tau eta kappa delta readGroup readInteger initial sourceAnswer answer
    sourceWeight weight parent
  have heq : (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta readGroup readInteger initial parent).cost
      (Sum.elim sourceAnswer (fun child => answer child.val.val))
      (Sum.elim sourceWeight (fun child => weight child.val.val)) = _ := hcost
  calc
    _ = (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta readGroup readInteger initial parent).cost
        (Sum.elim sourceAnswer (fun child => answer child.val.val))
        (Sum.elim sourceWeight (fun child => weight child.val.val)) := by
      congr 1 <;> (funext key; cases key <;> rfl)
    _ = _ := heq.trans (physicalRandomGlobalQuery_refinement_cost source target N P F exponent H Q T S
      copies factor multiplier tau eta kappa delta readGroup readInteger initial sourceAnswer answer
      sourceWeight weight parent.val hindex hbelow hshort)

end Cost

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRandomIndexCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Costs

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R → (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ) (answer : PhysicalTableRequest M J target.length → ℚ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
  (hindex : T < parent.val.index) (hbelow : parent.val.node.1.val < J)
  (hshort : ¬ (physicalSourceInterval source.length parent.val.node).hi -
    (physicalSourceInterval source.length parent.val.node).lo ≤ 1)

include hindex hbelow hshort

theorem chargedRandomGlobalQuery_earlier_cost :
    (chargedRandomGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial (Sum.inr parent)).cost
      (Sum.elim sourceAnswer (fun child => Sum.elim (fun entry => (initial entry : ℚ))
        (fun r => answer r.val) child.val))
      (Sum.elim (fun _ => 0) (fun child => chargedEarlierWeight (Sum.inr parent) child.val)) =
    (physicalRandomDataRequestQuery source target N P F exponent H Q tau
      (refinementFactor (factor parent.val.pass) F) eta kappa delta parent.val.pass parent.val.copy T S
      (parent.val.index - T) (Nat.sub_pos_of_lt hindex) parent.val.node hbelow
      (readGroup parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩ (Fin.ofNat R (parent.val.index - T - 1)))
      (readInteger parent.val.pass parent.val.copy ⟨parent.val.node, hbelow⟩ (Fin.ofNat R (parent.val.index - T - 1)))
      parent.val.state).cost
      (Sum.elim sourceAnswer (fun child => answer child.val))
      (Sum.elim (fun _ => 0) (fun child => physicalEarlierReadWeight (T + (parent.val.index - T)) child.val)) := by
  simp only [chargedEarlierWeight_table]
  rw [chargedRandomGlobalQuery_refinement_cost source target N P F exponent H Q T S passes copies
    factor multiplier tau eta kappa delta readGroup readInteger initial sourceAnswer answer (fun _ => 0) _ _ parent hindex hbelow hshort]
  have hrank : (PhysicalTableRequest.refinement parent.val.pass parent.val.copy parent.val.node
      T (parent.val.index - T) parent.val.state).rank T S = parent.val.rank T S := by
    unfold PhysicalTableRequest.refinement PhysicalTableRequest.rank
    dsimp only
    congr 1
    omega
  rw [← hrank]
  exact physicalRandomDataRequest_earlier_rank_cost source target N P F exponent H Q tau
    (refinementFactor (factor parent.val.pass) F) eta kappa delta parent.val.pass parent.val.copy T S
    (parent.val.index - T) (Nat.sub_pos_of_lt hindex) parent.val.node hbelow _ _ sourceAnswer parent.val.state answer

end Costs

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_InitialInputBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local initial cone uses a bounded number of preceding-seed
queries on every clamped seed, independently of an accuracy event. -/

namespace EditApproximation

theorem localTargetStates_length_from_scale {n : ℕ} (P b radius C : ℕ)
    (q : TargetInterval n) (hP : 0 < P) (hradius : radius ≤ C * b) :
    (localTargetStates n (seedGridSpacing b P) radius q).length ≤ (4 * C * P + 2) ^ 2 := by
  have hg : 0 < seedGridSpacing b P := by unfold seedGridSpacing; omega
  have hcover : b ≤ 2 * P * seedGridSpacing b P := by
    have hquot : b / P ≤ seedGridSpacing b P := le_max_right _ _
    have hdiv := Nat.lt_mul_div_succ b hP
    nlinarith only [hquot, hdiv, hg]
  have hprod : 2 * radius ≤ 4 * C * P * seedGridSpacing b P := by
    nlinarith only [hradius, Nat.mul_le_mul_left (2 * C) hcover]
  have hcount : 2 * radius / seedGridSpacing b P ≤ 4 * C * P := by
    have hdivision := Nat.div_mul_le_self (2 * radius) (seedGridSpacing b P)
    nlinarith only [hdivision, hprod, hg]
  exact (localTargetStates_length_le hg q).trans
    (Nat.pow_le_pow_left (Nat.add_le_add_right hcount 2) 2)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RefinementSupportBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cardinality of the actual raw initial-data and band-data lists. The
counts apply before any good-seed event and include rejected candidates. -/

namespace EditApproximation

theorem list_eraseDups_length_le {α : Type*} [BEq α] (items : List α) :
    items.eraseDups.length ≤ items.length := by
  cases items with
  | nil => exact le_rfl
  | cons first rest =>
    rw [List.eraseDups_cons, List.length_cons, List.length_cons]
    exact Nat.succ_le_succ ((list_eraseDups_length_le _).trans (List.length_filter_le _ _))
termination_by items.length
decreasing_by
  have h := List.length_filter_le (fun b => !b == first) rest
  simp only [List.length_cons]
  omega

theorem rawRefinementCenters_length {n : ℕ} (N P F : ℕ) (a value : ℚ)
    (q : TargetInterval n) (hP : 0 < P) (hF : 1 ≤ F) :
    (rawRefinementCenters N P F a value q).length ≤
      (dyadicQueryWindow N value a F).length * (64 * F * P + 2) ^ 2 := by
  apply (list_eraseDups_length_le _).trans
  apply list_flatMap_length_le
  intro b hb
  have hwindow := of_decide_eq_true (List.mem_filter.mp hb).2
  have hceil : ⌈value⌉₊ ≤ 16 * F * b := by
    apply Nat.ceil_le.mpr
    have h := (div_le_iff₀ (by positivity : (0 : ℚ) < 16 * F)).mp hwindow.1
    push_cast
    nlinarith only [h]
  simpa only [show 4 * (16 * F) * P = 64 * F * P by ring] using
    localTargetStates_length_from_scale P b ⌈value⌉₊ (16 * F) q hP hceil

theorem wideWarmupInputs_length {nx ny M : ℕ} (parent : TargetInterval nx) (P : ℕ)
    (representatives : List (ℕ × TargetInterval ny)) (hP : 0 < P) :
    (wideWarmupInputs (M := M) parent P representatives).length ≤
      representatives.length * M * (40 * P + 2) ^ 2 := by
  apply (list_eraseDups_length_le _).trans
  have h : (representatives.flatMap fun br => (List.finRange M).flatMap fun i =>
      (wideChildStateList parent br.2 br.1 P i).map fun r => (i, r)).length ≤
      representatives.length * (M * (40 * P + 2) ^ 2) := by
    apply list_flatMap_length_le
    intro br hbr
    have hi : ((List.finRange M).flatMap fun i =>
        (wideChildStateList parent br.2 br.1 P i).map fun r => (i, r)).length ≤
        (List.finRange M).length * (40 * P + 2) ^ 2 := by
      apply list_flatMap_length_le
      intro i hi
      simpa only [List.length_map] using wideEarlierChildStateList_length_le parent br.2 br.1 P hP i
    simpa only [List.length_finRange] using hi
  exact h.trans_eq (by ring)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_WarmupReadWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal seed, initial-cone and warmup query counts. No accuracy event
is needed: even rejected local centers are included in these bounds. -/

namespace EditApproximation

theorem rawInitialConeCenters_length {n : ℕ} (N P Amax : ℕ) (A : ℚ)
    (value : ℕ) (q : TargetInterval n) (hP : 0 < P) (hA : 1 ≤ A) (hmax : A ≤ Amax) :
    (rawInitialConeCenters N P A value q).length ≤
      (dyadicScales N).length * (64 * Amax ^ 2 * P + 2) ^ 2 := by
  unfold rawInitialConeCenters
  apply (list_flatMap_length_le _ _ _ ?_).trans
    (Nat.mul_le_mul_right _ (List.length_filter_le _ _))
  intro b hb
  have hwindow := of_decide_eq_true (List.mem_filter.mp hb).2
  have hApos : 0 < A := by linarith
  have hscale : (value : ℚ) ≤ 16 * A ^ 2 * b := by
    have h := (div_le_iff₀ (by positivity : (0 : ℚ) < 16 * A ^ 2)).mp hwindow.1
    nlinarith only [h]
  have hAsq : A ^ 2 ≤ (Amax : ℚ) ^ 2 := pow_le_pow_left₀ hApos.le hmax 2
  have hradius : value ≤ 16 * Amax ^ 2 * b := by
    have hmul := mul_le_mul_of_nonneg_right hAsq (by positivity : (0 : ℚ) ≤ 16 * b)
    have h : (value : ℚ) ≤ (16 * Amax ^ 2 * b : ℕ) := by
      push_cast
      nlinarith only [hscale, hmul]
    exact_mod_cast h
  simpa only [show 4 * (16 * Amax ^ 2) * P = 64 * Amax ^ 2 * P by ring] using
    localTargetStates_length_from_scale P b value (16 * Amax ^ 2) q hP hradius

theorem physicalInitialQuery_cost_le {ι α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (N P F Amax seedCost : ℕ) (A : ℚ)
    (seedRead : PhysicalEntry M J target.length → FiniteQuery ι)
    (node : PhysicalNode M J) (q : TargetInterval target.length) (oracle : ι → ℚ)
    (hP : 0 < P) (hA : 1 ≤ A) (hmax : A ≤ Amax)
    (hseed : ∀ r, (seedRead (node, r)).cost oracle (fun _ => 1) ≤ seedCost) :
    (physicalInitialQuery source target N P F A seedRead (node, q)).cost oracle (fun _ => 1) ≤
      (1 + (dyadicScales N).length * (64 * Amax ^ 2 * P + 2) ^ 2) * seedCost := by
  unfold physicalInitialQuery
  dsimp only
  split_ifs
  · exact Nat.zero_le _
  · rw [FiniteQuery.cost_bind]
    have hkeys := rawInitialConeCenters_length N P Amax A
      ⌈(seedRead (node, q)).value oracle⌉₊ q hP hA hmax
    rw [FiniteQuery.cost_collect]
    simp only [FiniteQuery.cost, Nat.add_zero]
    have hc := list_map_sum_le_constant
      (rawInitialConeCenters N P A ⌈(seedRead (node, q)).value oracle⌉₊ q)
      (fun r => (seedRead (node, r)).cost oracle (fun _ => 1)) seedCost
      (fun r => hseed r)
    calc
      _ ≤ seedCost + (rawInitialConeCenters N P A
          ⌈(seedRead (node, q)).value oracle⌉₊ q).length * seedCost :=
        Nat.add_le_add (hseed q) hc
      _ ≤ seedCost + ((dyadicScales N).length * (64 * Amax ^ 2 * P + 2) ^ 2) * seedCost := by
        simpa only [Nat.add_zero] using Nat.add_le_add_left (Nat.mul_le_mul_right seedCost hkeys) seedCost
      _ = _ := by ring

theorem localWarmupStepQuery_cost_le {ι : Type*} {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F window initialCost childCost : ℕ) (a : ℚ)
    (initialRead : TargetInterval ny → FiniteQuery ι)
    (childRead : Fin M × TargetInterval ny → FiniteQuery ι)
    (oracle : ι → ℚ) (q : TargetInterval ny) (hP : 0 < P) (hF : 1 ≤ F)
    (hwindow : ∀ w, (dyadicQueryWindow N w a F).length ≤ window)
    (hinitial : ∀ r, (initialRead r).cost oracle (fun _ => 1) ≤ initialCost)
    (hchild : ∀ input, (childRead input).cost oracle (fun _ => 1) ≤ childCost) :
    (localWarmupStepQuery parent N P F a initialRead childRead q).cost oracle (fun _ => 1) ≤
      (1 + window * (64 * F * P + 2) ^ 2) * initialCost +
        window * (64 * F * P + 2) ^ 2 * M * (40 * P + 2) ^ 2 * childCost := by
  let value := (initialRead q).value oracle
  let centers := rawRefinementCenters N P F a value q
  have hcenters : centers.length ≤ window * (64 * F * P + 2) ^ 2 :=
    (rawRefinementCenters_length N P F a value q hP hF).trans
      (Nat.mul_le_mul_right _ (hwindow value))
  have hnext (answers : List ℚ) :
      (FiniteQuery.collect childRead
        (wideWarmupInputs (M := M) parent P
          (localRefinementRepresentatives N P F a
            (fun r => if r = q then value else finiteAnswerTable centers answers r) q))
        (fun values => .done (rationalBellman (M := M)
          (fun r => if r = q then value else finiteAnswerTable centers answers r)
          (fun q r => targetEndpointDistance q r) (128 * F)
          (rationalActualWideActions parent
            (localRefinementRepresentatives N P F a
              (fun r => if r = q then value else finiteAnswerTable centers answers r) q) P)
          (finiteAnswerTable (wideWarmupInputs (M := M) parent P
            (localRefinementRepresentatives N P F a
              (fun r => if r = q then value else finiteAnswerTable centers answers r) q)) values) q))).cost oracle (fun _ => 1) ≤
        window * (64 * F * P + 2) ^ 2 * M * (40 * P + 2) ^ 2 * childCost := by
    have hreps := localRefinementRepresentatives_length N P F a
      (fun r => if r = q then value else finiteAnswerTable centers answers r) q hP hF
    have hlen := (wideWarmupInputs_length (M := M) parent P _ hP).trans
      (Nat.mul_le_mul_right ((40 * P + 2) ^ 2) (Nat.mul_le_mul_right M
        (hreps.trans (Nat.mul_le_mul_right _ (hwindow _)))))
    rw [FiniteQuery.cost_collect]
    simp only [FiniteQuery.cost, Nat.add_zero]
    exact (list_map_sum_le_constant _ (fun input => (childRead input).cost oracle (fun _ => 1))
      childCost (fun input => hchild input)).trans (Nat.mul_le_mul_right childCost hlen)
  unfold localWarmupStepQuery
  rw [FiniteQuery.cost_bind]
  rw [FiniteQuery.cost_collect]
  have hc := Nat.add_le_add
    (list_map_sum_le_constant centers (fun r => (initialRead r).cost oracle (fun _ => 1)) initialCost hinitial)
    (hnext (centers.map fun r => (initialRead r).value oracle))
  calc
    _ ≤ initialCost + (centers.length * initialCost +
        window * (64 * F * P + 2) ^ 2 * M * (40 * P + 2) ^ 2 * childCost) :=
      Nat.add_le_add (hinitial q) hc
    _ ≤ initialCost + (window * (64 * F * P + 2) ^ 2 * initialCost +
        window * (64 * F * P + 2) ^ 2 * M * (40 * P + 2) ^ 2 * childCost) :=
      Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul_right initialCost hcenters) _) _
    _ = _ := by ring

theorem chargedSeedQuery_cost_le {M J ny passes copies T S : ℕ} (N : ℕ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J ny // r.Bounded passes copies T S})
    (state : PhysicalEntry M J ny) (oracle) :
    (chargedSeedQuery N multiplier parent state).cost oracle (fun _ => 1) ≤ max 1 copies := by
  rw [chargedSeedQuery_cost]
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _
  · exact Nat.zero_le _

theorem chargedWarmupQuery_cost_le {α : Type*} [DecidableEq α] {M J passes copies T S : ℕ}
    (source target : List α) (N P F Amax window : ℕ)
    (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (oracle) (hP : 0 < P) (hF : 1 ≤ F) (hA : 1 ≤ factor parent.val.pass)
    (hmax : factor parent.val.pass ≤ Amax)
    (hwindow : ∀ w, (dyadicQueryWindow N w (refinementFactor (factor parent.val.pass) F) F).length ≤ window) :
    (chargedWarmupQuery source target N P F factor multiplier parent).cost oracle (fun _ => 1) ≤
      (1 + window * (64 * F * P + 2) ^ 2) *
        ((1 + (dyadicScales N).length * (64 * Amax ^ 2 * P + 2) ^ 2) * max 1 copies) +
        window * (64 * F * P + 2) ^ 2 * M * (40 * P + 2) ^ 2 := by
  let initialCost := (1 + (dyadicScales N).length * (64 * Amax ^ 2 * P + 2) ^ 2) * max 1 copies
  have hinitial (r : TargetInterval target.length) :
      (physicalInitialQuery source target N P F (factor parent.val.pass)
        (chargedSeedQuery N multiplier parent) (parent.val.node, r)).cost oracle (fun _ => 1) ≤ initialCost :=
    physicalInitialQuery_cost_le source target N P F Amax (max 1 copies) _ _ _ r oracle hP hA hmax
      (fun s => chargedSeedQuery_cost_le N multiplier parent _ oracle)
  have hinitialBound : initialCost ≤
      (1 + window * (64 * F * P + 2) ^ 2) * initialCost +
        window * (64 * F * P + 2) ^ 2 * M * (40 * P + 2) ^ 2 := by
    exact (Nat.le_mul_of_pos_left initialCost (by omega)).trans (Nat.le_add_right _ _)
  unfold chargedWarmupQuery
  split_ifs with hz hbelow hshort
  · exact (hinitial _).trans hinitialBound
  · exact (hinitial _).trans hinitialBound
  · unfold physicalWarmupStepQuery
    simpa only [Nat.mul_one] using localWarmupStepQuery_cost_le
      (physicalSourceInterval source.length parent.val.node) N P F window initialCost 1
      (refinementFactor (factor parent.val.pass) F) _ _ oracle parent.val.state hP hF hwindow hinitial
      (fun input => by simp only [chargedWarmupChild, FiniteQuery.cost, Nat.add_zero, le_refl])
  · exact (hinitial _).trans hinitialBound

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteQueryCostOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation.FiniteQuery

theorem cost_mono_weights {ι : Type*} (oracle : ι → ℚ) (program : FiniteQuery ι)
    (left right : ι → ℕ) (hle : ∀ key, left key ≤ right key) :
    program.cost oracle left ≤ program.cost oracle right := by
  induction program with
  | done result => exact le_rfl
  | read key next ih => exact Nat.add_le_add (hle key) (ih (oracle key))

theorem cost_zero {ι : Type*} (oracle : ι → ℚ) (program : FiniteQuery ι) :
    program.cost oracle (fun _ => 0) = 0 := by
  induction program with
  | done result => rfl
  | read key next ih => simpa only [cost, Nat.zero_add] using ih (oracle key)

end EditApproximation.FiniteQuery

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCurrentQueryBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial same-index call budget after substituting the
computed window, cell, scale-label, sampling and rounding parameters. -/

namespace EditApproximation

theorem computed_window_exponent_bound (N : ℕ) (hN : 0 < N) (hell : 8 ≤ inputSmallLog N) :
    computedSeedInitialExponent N + 8 ≤ 2 * inputSmallLog N ^ 2 := by
  have hh := (inputSmallLog_bounds N hN).1
  have hp : coarseExponent (inputSmallLog N) ≤ inputSmallLog N :=
    (Nat.sqrt_le_self _).trans ((Nat.sqrt_le_self _).trans (Nat.log_le_self _ _))
  have hmul := Nat.mul_le_mul (Nat.add_le_add_right hp 4) hh
  unfold computedSeedInitialExponent
  have hslack : 4 * inputSmallLog N + 8 ≤ inputSmallLog N ^ 2 := by nlinarith
  nlinarith only [hmul, hslack]

theorem computed_refinement_window (N : ℕ) (hN : 0 < N) (hell : 8 ≤ inputSmallLog N)
    (A w : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ)) :
    (dyadicQueryWindow N w (refinementFactor A (inputSmallLog N)) (inputSmallLog N)).length ≤
      computedSeedInitialExponent N + 8 := by
  have hh := inputSmallLog_bounds N hN
  have hf : smallLogExponent N ≤ inputSmallLog N := (smallLogExponent N).lt_two_pow_self.le
  have he0 : smallLogExponent N ≤ computedSeedInitialExponent N := by
    have hfour := Nat.mul_le_mul_right (heightExponent N)
      (show 4 ≤ coarseExponent (inputSmallLog N) + 4 by omega)
    unfold computedSeedInitialExponent
    nlinarith only [hh.2, hf, hfour]
  apply refinement_query_window_length N (inputSmallLog N) (computedSeedInitialExponent N) A w (by omega)
  · simpa only [inputSmallLog, Nat.cast_pow, Nat.cast_ofNat] using
      pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) he0
  · exact hA.trans_eq (computedSeed_initial_factor N).symm

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedEarlierInputBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual earlier-input cover satisfies the polynomial branching
budget at every seed, after substituting the computed time and grid
parameters. -/

namespace EditApproximation

theorem computed_smallLog_le_height (N : ℕ) : inputSmallLog N ≤ inputHeight N := by
  have hf : smallLogExponent N ≤ heightExponent N := by
    unfold smallLogExponent
    apply Nat.clog_le_of_le_pow
    exact max_le Nat.one_le_two_pow (heightExponent N).lt_two_pow_self.le
  exact pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hf

theorem computed_window_le_height_cube (N : ℕ) (hN : 0 < N)
    (hell : 8 ≤ inputSmallLog N) (hH : 2 ≤ inputHeight N) :
    computedSeedInitialExponent N + 8 ≤ inputHeight N ^ 3 := by
  calc
    _ ≤ 2 * inputSmallLog N ^ 2 := computed_window_exponent_bound N hN hell
    _ ≤ inputHeight N * inputHeight N ^ 2 :=
      Nat.mul_le_mul hH (Nat.pow_le_pow_left (computed_smallLog_le_height N) 2)
    _ = _ := by ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedRandomPhysicalCost
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

section Physical

variable {σ α : Type*} (source target : List α) {M J : ℕ} [NeZero M]
  (N P H : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
  (hM : M = (integerParameters N).M) (hP : P = (integerParameters N).P)
  (A tau eta kappa delta : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ))
  (pass copy T S t : ℕ) (hT : T = (integerParameters N).T)
  (ht : 0 < t) (htime : t ≤ (integerParameters N).S)
  (node : PhysicalNode M J) (hbelow : node.1.val < J)
  (readGroup : GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery σ)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (q : TargetInterval target.length) (sourceAnswer : σ → ℚ)
  (answer : PhysicalTableRequest M J target.length → ℚ)
  (hw : 0 ≤ answer (PhysicalTableRequest.warmup pass copy node 0 q))

include hN hell hM hP hA hT ht htime hw

 theorem computed_physicalRandom_earlier_reads :
    (physicalRandomDataRequestQuery source target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) tau (refinementFactor A (inputSmallLog N)) eta kappa delta
      pass copy T S t ht node hbelow readGroup readInteger q).cost
      (Sum.elim sourceAnswer (fun key => answer key.val))
      (Sum.elim (fun _ => 0) (fun key => physicalEarlierReadWeight (T + t) key.val)) ≤
        inputHeight N ^ (257 * (coarseExponent (inputSmallLog N) + 1)) := by
  unfold physicalRandomDataRequestQuery
  refine (computed_localRandomDataQuery_table_cost source target _ N P H T t hN hell hM hP hT
    ht htime A tau eta kappa delta hA _ _ _ _ _ q _ _ _ _ 1 1 0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
  · intro r
    rw [FiniteQuery.mapKeys_cost]
    exact (physicalRefinementWarmupRead_cost_earlier pass copy T S t ht node q node le_rfl
      0 (Nat.zero_le T) r _).le
  · intro input
    rw [FiniteQuery.mapKeys_cost]
    simpa only [Nat.mul_one, Function.comp_def, Sum.elim_inr] using
      (physicalRefinementMassQuery_cost_earlier pass copy T S t ht node hbelow q input _).le
  · intro input
    rw [FiniteQuery.mapKeys_cost]
    exact (physicalRefinementWarmupRead_cost_earlier pass copy T S t ht node q
      (physicalChild node hbelow input.1) _ 0 (Nat.zero_le T) input.2 _).le
  · intro key
    rw [FiniteQuery.mapKeys_cost]
    exact FiniteQuery.cost_zero _ _
  · intro key range
    rw [FiniteQuery.mapKeys_cost]
    exact FiniteQuery.cost_zero _ _
  · intro input
    rw [FiniteQuery.mapKeys_cost]
    exact physicalRefinementEarlierQuery_cost_earlier pass copy T S t node hbelow q input _
  · intro input
    rw [FiniteQuery.mapKeys_cost]
    exact (physicalRefinementCurrentQuery_cost_earlier pass copy T S t node hbelow q input _).le
  · exact hw
  · simp only [Nat.mul_one, Nat.mul_zero, Nat.add_zero]
    let B := inputHeight N ^ (256 * (coarseExponent (inputSmallLog N) + 1))
    have hH : 64 ≤ inputHeight N :=
      (by omega : 64 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
    have hB : 1 ≤ B := one_le_pow₀ (by omega)
    change 2 + 2 * B + B ≤ _
    calc
      _ ≤ 5 * B := by omega
      _ ≤ inputHeight N * B := Nat.mul_le_mul_right B (by omega)
      _ = inputHeight N ^ (1 + 256 * (coarseExponent (inputSmallLog N) + 1)) := by
        dsimp only [B]
        rw [pow_add, pow_one]
      _ ≤ _ := pow_le_pow_right₀ (by omega) (by omega)

end Physical

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedWarmupReadBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial earlier-edge bound for the complete charged warmup
query. It includes all preceding-pass copy reads and pass-zero coarse
reads used by its initial cones. -/

namespace EditApproximation

theorem warmupReadBudget_box (Z scales window P F Amax M copies : ℕ)
    (hZ : 64 ≤ Z) (hscales : scales ≤ Z) (hwindow : window ≤ Z)
    (hP : P ≤ Z) (hF : F ≤ Z) (hA : Amax ≤ Z) (hM : M ≤ Z)
    (hcopies : copies ≤ Z) : warmupReadBudget scales window P F Amax M copies ≤ Z ^ 24 := by
  have hZone : 1 ≤ Z := by omega
  have hZtwo : 2 ≤ Z := by omega
  have hbase (c x : ℕ) (hc : c ≤ Z) (hx : 2 ≤ x) : c * x + 2 ≤ Z ^ 2 * x := by
    have hcx := Nat.mul_le_mul_right x hc
    have hzx : 2 ≤ Z * x := hx.trans (Nat.le_mul_of_pos_left x hZone)
    have hcoeff := Nat.mul_le_mul_right x (show 2 * Z ≤ Z ^ 2 by nlinarith only [hZtwo])
    nlinarith only [hcx, hzx, hcoeff]
  have hadd (k : ℕ) : 1 + Z ^ k ≤ Z ^ (k + 1) := by
    have hp : 1 ≤ Z ^ k := one_le_pow₀ hZone
    have hm := Nat.mul_le_mul_right (Z ^ k) hZtwo
    rw [pow_succ]
    nlinarith only [hp, hm]
  have h64 : 64 ≤ Z := hZ
  have h40 : 40 ≤ Z := by omega
  have hsmall : 64 * F * P + 2 ≤ Z ^ 4 := by
    calc
      _ ≤ 64 * Z * Z + 2 := Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_left 64 hF) hP) 2
      _ ≤ _ := by
        first | (convert hbase 64 (Z ^ 2) h64 ((Nat.pow_le_pow_left hZtwo 2).trans' (by norm_num)) using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans ((hbase 64 (Z ^ 2) h64 ((Nat.pow_le_pow_left hZtwo 2).trans' (by norm_num))).trans (le_of_eq (by ring)))
  have hinitialBase : 64 * Amax ^ 2 * P + 2 ≤ Z ^ 5 := by
    calc
      _ ≤ 64 * Z ^ 2 * Z + 2 :=
        Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left hA 2)) hP) 2
      _ ≤ _ := by
        first | (convert hbase 64 (Z ^ 3) h64 ((Nat.pow_le_pow_left hZtwo 3).trans' (by norm_num)) using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans ((hbase 64 (Z ^ 3) h64 ((Nat.pow_le_pow_left hZtwo 3).trans' (by norm_num))).trans (le_of_eq (by ring)))
  have hwideBase : 40 * P + 2 ≤ Z ^ 3 := by
    calc
      _ ≤ 40 * Z + 2 := Nat.add_le_add_right (Nat.mul_le_mul_left 40 hP) 2
      _ ≤ _ := by convert hbase 40 Z h40 hZtwo using 1 <;> first | rfl | ring
  have hraw : window * (64 * F * P + 2) ^ 2 ≤ Z ^ 9 := by
    exact (Nat.mul_le_mul hwindow (Nat.pow_le_pow_left hsmall 2)).trans_eq (by ring)
  have hrawInitial : scales * (64 * Amax ^ 2 * P + 2) ^ 2 ≤ Z ^ 11 := by
    exact (Nat.mul_le_mul hscales (Nat.pow_le_pow_left hinitialBase 2)).trans_eq (by ring)
  have hinit : (1 + scales * (64 * Amax ^ 2 * P + 2) ^ 2) * max 1 copies ≤ Z ^ 13 := by
    exact (Nat.mul_le_mul ((Nat.add_le_add_left hrawInitial 1).trans (hadd 11))
      (max_le hZone hcopies)).trans_eq (by ring)
  have hfirst : (1 + window * (64 * F * P + 2) ^ 2) *
      ((1 + scales * (64 * Amax ^ 2 * P + 2) ^ 2) * max 1 copies) ≤ Z ^ 23 := by
    exact (Nat.mul_le_mul ((Nat.add_le_add_left hraw 1).trans (hadd 9)) hinit).trans_eq (by ring)
  have hsecond : window * (64 * F * P + 2) ^ 2 * M * (40 * P + 2) ^ 2 ≤ Z ^ 23 := by
    calc
      _ ≤ Z ^ 9 * Z * (Z ^ 3) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul hraw hM) (Nat.pow_le_pow_left hwideBase 2)
      _ = Z ^ 16 := by ring
      _ ≤ _ := pow_le_pow_right₀ hZone (by decide)
  exact (Nat.add_le_add hfirst hsecond).trans (by
    have hm := Nat.mul_le_mul_right (Z ^ 23) hZtwo
    have heq : Z ^ 24 = Z ^ 23 * Z := pow_succ Z 23
    calc
      Z ^ 23 + Z ^ 23 = 2 * Z ^ 23 := (two_mul _).symm
      _ ≤ Z * Z ^ 23 := hm
      _ = Z ^ 24 := by rw [heq]; exact Nat.mul_comm _ _)

theorem computed_dyadicScales_length (N : ℕ) (hH : 2 ≤ inputHeight N) :
    (dyadicScales N).length ≤ inputHeight N ^ 2 := by
  have hlog : Nat.log 2 N ≤ inputHeight N := by
    apply (Nat.log_le_clog 2 N).trans
    apply (Nat.clog_mono_right 2 (Nat.le_add_right N 2)).trans
    exact Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (Nat.clog 2 (N + 2))
  simp only [dyadicScales, List.length_map, List.length_range]
  nlinarith only [hlog, hH]

theorem computed_warmupReadBudget_le (N M P copies : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) (hM : M = (integerParameters N).M)
    (hP : P = (integerParameters N).P) (hcopies : copies ≤ inputHeight N ^ 2) :
    warmupReadBudget (dyadicScales N).length (computedSeedInitialExponent N + 8)
      P (inputSmallLog N) (integerParameters N).initialFactor M copies ≤
      inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1)) := by
  let H := inputHeight N
  let p := coarseExponent (inputSmallLog N)
  let Z := H ^ (p + 20)
  have hF := computed_smallLog_le_height N
  have hH : 64 ≤ H := (by omega : 64 ≤ inputSmallLog N).trans hF
  have hZone : 1 ≤ H := by omega
  have hHZ : H ≤ Z := by
    calc
      H = H ^ 1 := (pow_one H).symm
      _ ≤ H ^ (p + 20) := pow_le_pow_right₀ hZone (by omega)
  have hH2Z : H ^ 2 ≤ Z := pow_le_pow_right₀ hZone (by omega)
  have hH3Z : H ^ 3 ≤ Z := pow_le_pow_right₀ hZone (by omega)
  have hscales : (dyadicScales N).length ≤ Z := (computed_dyadicScales_length N (by omega)).trans hH2Z
  have hwindow : computedSeedInitialExponent N + 8 ≤ Z :=
    (computed_window_le_height_cube N hN (by omega) (by omega)).trans hH3Z
  have hPZ : P ≤ Z := by change P ≤ (integerParameters N).P; exact hP.le
  have hAZ : (integerParameters N).initialFactor ≤ Z :=
    pow_le_pow_right₀ hZone (by omega)
  have hMZ : M ≤ Z := by
    rw [hM]
    exact (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (Nat.div_le_self _ _)).trans hHZ
  have hbound := warmupReadBudget_box Z (dyadicScales N).length (computedSeedInitialExponent N + 8)
    P (inputSmallLog N) (integerParameters N).initialFactor M copies (hH.trans hHZ)
    hscales hwindow hPZ (hF.trans hHZ) hAZ hMZ (hcopies.trans hH2Z)
  apply hbound.trans
  dsimp only [Z]
  rw [← pow_mul]
  exact pow_le_pow_right₀ hZone (by dsimp only [p]; omega)

theorem computed_chargedWarmupQuery_reads {α : Type*} [DecidableEq α]
    {M J passes copies T S : ℕ} (source target : List α) (N P : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
    (hM : M = (integerParameters N).M) (hP : P = (integerParameters N).P)
    (hcopies : copies ≤ inputHeight N ^ 2) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (oracle) (hA : 1 ≤ factor parent.val.pass)
    (hAmax : factor parent.val.pass ≤ ((integerParameters N).initialFactor : ℚ)) :
    (chargedWarmupQuery source target N P (inputSmallLog N) factor multiplier parent).cost
      oracle (fun _ => 1) ≤ inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1)) := by
  have hPpos : 0 < P := by
    rw [hP]
    change 0 < inputHeight N ^ _
    exact pow_pos (Nat.two_pow_pos _) _
  exact (chargedWarmupQuery_cost_le source target N P (inputSmallLog N)
    (integerParameters N).initialFactor (computedSeedInitialExponent N + 8) factor multiplier parent oracle
    hPpos (by omega) hA hAmax (fun w => computed_refinement_window N hN (by omega)
      (factor parent.val.pass) w hAmax)).trans
      (computed_warmupReadBudget_le N M P copies hN hell hM hP hcopies)

theorem computed_chargedInitialQuery_reads {α : Type*} [DecidableEq α]
    {M J passes copies T S : ℕ} (source target : List α) (N P : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
    (hM : M = (integerParameters N).M) (hP : P = (integerParameters N).P)
    (hcopies : copies ≤ inputHeight N ^ 2) (factor : ℕ → ℚ) (multiplier : ℕ → ℕ)
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (oracle) (hA : 1 ≤ factor parent.val.pass)
    (hAmax : factor parent.val.pass ≤ ((integerParameters N).initialFactor : ℚ)) :
    (physicalInitialQuery source target N P (inputSmallLog N) (factor parent.val.pass)
      (chargedSeedQuery N multiplier parent) (parent.val.node, parent.val.state)).cost oracle (fun _ => 1) ≤
      inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1)) := by
  have hPpos : 0 < P := by
    rw [hP]
    change 0 < inputHeight N ^ _
    exact pow_pos (Nat.two_pow_pos _) _
  let initialCost := (1 + (dyadicScales N).length *
    (64 * (integerParameters N).initialFactor ^ 2 * P + 2) ^ 2) * max 1 copies
  have hi : (physicalInitialQuery source target N P (inputSmallLog N) (factor parent.val.pass)
      (chargedSeedQuery N multiplier parent) (parent.val.node, parent.val.state)).cost oracle (fun _ => 1) ≤
      initialCost :=
    physicalInitialQuery_cost_le source target N P (inputSmallLog N) (integerParameters N).initialFactor
      (max 1 copies) _ _ _ _ oracle hPpos hA hAmax
      (fun r => chargedSeedQuery_cost_le N multiplier parent _ oracle)
  have hb : initialCost ≤ warmupReadBudget (dyadicScales N).length
      (computedSeedInitialExponent N + 8) P (inputSmallLog N) (integerParameters N).initialFactor M copies := by
    exact (Nat.le_mul_of_pos_left initialCost (by omega)).trans (Nat.le_add_right _ _)
  exact hi.trans (hb.trans (computed_warmupReadBudget_le N M P copies hN hell hM hP hcopies))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedChargedRandomBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform edge budgets for the actual charged global interpreter.
The bounds hold for every initial seed and every draw, including failed
approximation events. -/

namespace EditApproximation

section Current

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    CellGroupDraws M (inputSmallLog N) (inputSmallLog N ^ 80))
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

variable
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)

local notation "values" => localRequestValue source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S copies factor multiplier
    tau eta kappa delta group integer initial

variable (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
  (hM : M = (integerParameters N).M)
  (hAmax : ∀ pass, factor pass ≤ ((integerParameters N).initialFactor : ℚ))
  (hP : P = (integerParameters N).P) (hT : T = (integerParameters N).T)
  (hS : S = (integerParameters N).S)


variable (hcopies : copies ≤ inputHeight N ^ 2)
  (hAmin : ∀ pass, 1 ≤ factor pass)

include hN hell hM hAmax hP hT hS hcopies hAmin in
 theorem computed_chargedRandomGlobalQuery_earlier_reads_oai
    (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRandomGlobalQuery source target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta
      readGroup readInteger initial request).cost
      (Sum.elim sourceAnswer (fun child => chargedRequestValue source target N P (inputSmallLog N) (40 * smallLogExponent N)
        H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta
        group integer initial child.val))
      (Sum.elim (fun _ => 0) (fun child => chargedEarlierWeight request child.val)) ≤
        inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1)) := by
  cases request with
  | inl entry => exact Nat.zero_le _
  | inr parent =>
    let oracle := fun child : {child : ChargedPhysicalRequest M J target.length passes copies T S //
        child.rank < ChargedPhysicalRequest.rank (Sum.inr parent)} =>
      chargedRequestValue source target N P (inputSmallLog N) (40 * smallLogExponent N)
        H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta
        group integer initial child.val
    have hmono (program : FiniteQuery {child : ChargedPhysicalRequest M J target.length passes copies T S //
        child.rank < ChargedPhysicalRequest.rank (Sum.inr parent)}) :
        program.cost oracle (fun child => chargedEarlierWeight (Sum.inr parent) child.val) ≤
          program.cost oracle (fun _ => 1) := by
      apply FiniteQuery.cost_mono_weights
      intro child
      unfold chargedEarlierWeight
      split_ifs <;> omega
    by_cases hi : parent.val.index ≤ T
    · unfold chargedRandomGlobalQuery
      dsimp only
      rw [ite_eq_left hi, FiniteQuery.mapKeys_cost]
      simp only [Function.comp_def, Sum.elim_inr]
      exact (hmono _).trans (computed_chargedWarmupQuery_reads source target N P hN hell hM hP hcopies
        factor multiplier parent oracle (hAmin _) (hAmax _))
    · by_cases hb : parent.val.node.1.val < J
      · by_cases hs : (physicalSourceInterval source.length parent.val.node).hi -
            (physicalSourceInterval source.length parent.val.node).lo ≤ 1
        · unfold chargedRandomGlobalQuery
          dsimp only
          rw [ite_eq_right hi, ite_eq_left hb, ite_eq_left hs, FiniteQuery.mapKeys_cost]
          simp only [Function.comp_def, Sum.elim_inr]
          exact (hmono _).trans (computed_chargedInitialQuery_reads source target N P hN hell hM hP hcopies
            factor multiplier parent oracle (hAmin _) (hAmax _))
        · have hanswer : chargedRequestValue source target N P (inputSmallLog N)
              (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
              tau eta kappa delta group integer initial =
              Sum.elim (fun entry => (initial entry : ℚ)) (fun r => values r.val) := by
            funext key
            cases key <;> rfl
          rw [hanswer]
          rw [chargedRandomGlobalQuery_earlier_cost source target N P (inputSmallLog N)
            (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
            tau eta kappa delta readGroup readInteger sourceAnswer values initial parent (by omega) hb hs]
          calc
            _ ≤ inputHeight N ^ (257 * (coarseExponent (inputSmallLog N) + 1)) := by
              apply computed_physicalRandom_earlier_reads source target N P H hN hell hM hP
                (factor parent.val.pass) tau eta kappa delta (hAmax _) parent.val.pass parent.val.copy
                T S (parent.val.index - T) hT (by omega)
                (by
                  have h := parent.property.2.2
                  have htime : parent.val.index - T ≤ S := by omega
                  exact htime.trans_eq hS) parent.val.node hb
              rw [localRequestValue_initial]
              exact stageInitial_nonneg_all_seeds _ _ _ _ _ _ _ _
            _ ≤ _ := pow_le_pow_right₀ (Nat.one_le_two_pow) (by omega)
      · unfold chargedRandomGlobalQuery
        dsimp only
        rw [ite_eq_right hi, ite_eq_right hb, FiniteQuery.mapKeys_cost]
        simp only [Function.comp_def, Sum.elim_inr]
        exact (hmono _).trans (computed_chargedInitialQuery_reads source target N P hN hell hM hP hcopies
          factor multiplier parent oracle (hAmin _) (hAmax _))

end Current

end EditApproximation

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.EditApproximation.computed_chargedRandomGlobalQuery_earlier_reads_oai.{u_1, u_2} := @OAI.EditApproximation.computed_chargedRandomGlobalQuery_earlier_reads_oai.{u_1, u_2}
