-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_forwardHighMask_guards
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:43:21.259494+00:00
-- url     : https://prove2.me/submissions/82a7fa43-c392-4ee1-b462-2c60c7be111f

import Mathlib
import Definitions.Def_OAIQ081S017
import Definitions.Def_OAIQ081S037
import Definitions.Def_OAIQ081S052
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CostAssembly_eventually_measured_guards

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer high-incidence cutoff and disjoint branching on original coordinates. -/
namespace SubexponentialSAT.SqrtLog.HighIncidence

open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
theorem high_mass_le (scope : E → Finset V) (cut : ℕ) :
    (high scope cut).card * (cut + 1) ≤ totalScope scope := by
  calc
    _ = ∑ _v ∈ high scope cut, (cut + 1) := by simp
    _ ≤ ∑ v ∈ high scope cut, Incidence.degree scope v := by
      apply Finset.sum_le_sum
      intro v hv
      exact Nat.succ_le_of_lt (Finset.mem_filter.mp hv).2
    _ ≤ ∑ v, Incidence.degree scope v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
    _ = totalScope scope := Incidence.sum_degrees scope

omit [DecidableEq E] in
theorem high_card_mul_le (scope : E → Finset V) (cut t : ℕ)
    (hbudget : totalScope scope * t ≤ Fintype.card V * cut) :
    (high scope cut).card * t ≤ Fintype.card V := by
  have hm := high_mass_le scope cut
  have hmul := Nat.mul_le_mul_right t hm
  by_cases hc : cut = 0
  · simp only [hc, Nat.mul_zero] at hbudget
    have hh : (high scope cut).card ≤ totalScope scope := by nlinarith
    have := (Nat.mul_le_mul_right t hh).trans hbudget
    omega
  · have hp : 0 < cut := Nat.pos_of_ne_zero hc
    have hsmall : (high scope cut).card * t * cut ≤ Fintype.card V * cut := by
      nlinarith
    exact Nat.le_of_mul_le_mul_right hsmall hp

end SubexponentialSAT.SqrtLog.HighIncidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PaddedCompletion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit padded completion leaves

Every optional coordinate branches over the entire word alphabet. A real
coordinate updates the assignment; a dummy coordinate ignores the word.
Padding therefore implements the common-denominator multiplicity by actual
finite leaves rather than a multiplication of the resulting score.
-/

namespace SubexponentialSAT.Subexp.PaddedCompletion

open SubexponentialSAT.LocalExpectation
open SubexponentialSAT.Subexp.LocalExpectation

variable {I W J : Type*} [DecidableEq I]

theorem trueCount_eq_count (bs : List Bool) :
    trueCount bs = bs.count true := by
  have h : (fun b : Bool => b == true) = id := by
    funext b
    cases b <;> rfl
  simp only [List.count_eq_countP, List.countP_eq_length_filter, h,
    trueCount, successful]

end SubexponentialSAT.Subexp.PaddedCompletion

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

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical mask is exactly the finite incidence cutoff on original
variables. The theorem counts zero-degree variables in the ambient dimension. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram
open scoped BigOperators

theorem highPrefix_trueCount (scopes : List (List ℕ)) (cut n : ℕ) :
    Branches.trueCount (highPrefix scopes cut n) =
      ∑ v ∈ Finset.range n, if cut < degree scopes v then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases h : cut < degree scopes n
      · simpa [highPrefix, h, Branches.trueCount, Subexp.PaddedCompletion.trueCount,
          Subexp.PaddedCompletion.successful, Nat.add_comm] using congrArg Nat.succ ih
      · simpa [highPrefix, h, Branches.trueCount, Subexp.PaddedCompletion.trueCount,
          Subexp.PaddedCompletion.successful] using ih

theorem highPrefix_count_eq_card (scopes : List (List ℕ)) (cut n : ℕ) :
    Branches.trueCount (highPrefix scopes cut n) =
      (HighIncidence.high (suppliedScope n scopes) cut).card := by
  rw [highPrefix_trueCount, Finset.sum_range]
  simp only [HighIncidence.high, Finset.card_eq_sum_ones, Finset.sum_filter,
    degree_suppliedScope]


/-- Even nonnormalized supplied records overcount rather than undercount mass.
This suffices for the high-dimension bound with the physically counted S. -/
theorem suppliedScope_card_le (n : ℕ) (scopes : List (List ℕ)) (e : Fin scopes.length) :
    (suppliedScope n scopes e).card ≤ (scopes.get e).length := by
  have hi : (suppliedScope n scopes e).image Fin.val ⊆ (scopes.get e).toFinset := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact List.mem_toFinset.mpr ((Subexp.IncidencePlanSpec.mem_pattern_scope n scopes v e).mp hv)
  calc
    _ = ((suppliedScope n scopes e).image Fin.val).card :=
      (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (scopes.get e).toFinset.card := Finset.card_le_card hi
    _ ≤ (scopes.get e).length := List.toFinset_card_le _

theorem suppliedScope_mass_le (n : ℕ) (scopes : List (List ℕ)) :
    HighIncidence.totalScope (suppliedScope n scopes) ≤ (scopes.map List.length).sum := by
  calc
    _ ≤ ∑ e : Fin scopes.length, (scopes.get e).length :=
      Finset.sum_le_sum (fun e _ => suppliedScope_card_le n scopes e)
    _ = (scopes.map List.length).sum := by
      rw [← Fin.sum_ofFn]
      change (List.ofFn (List.length ∘ scopes.get)).sum = _
      rw [← List.map_ofFn, List.ofFn_get]

/-- The threshold may be computed from raw entry counts. Duplicates or
out-of-range supplied IDs cannot invalidate the dimension estimate. -/
theorem computed_high_dimension_rawMass (scopes : List (List ℕ)) (n t : ℕ)
    (hn : 0 < n) (ht : 0 < t) :
    Branches.trueCount
      (highPrefix scopes (((scopes.map List.length).sum * t) ⌈/⌉ n) n) ≤ n / t := by
  rw [highPrefix_count_eq_card]
  apply (Nat.le_div_iff_mul_le ht).mpr
  have hb : HighIncidence.totalScope (suppliedScope n scopes) * t ≤
      n * (((scopes.map List.length).sum * t) ⌈/⌉ n) := by
    calc
      _ ≤ (scopes.map List.length).sum * t := Nat.mul_le_mul_right _ (suppliedScope_mass_le n scopes)
      _ ≤ n * (((scopes.map List.length).sum * t) ⌈/⌉ n) :=
        (ceilDiv_le_iff_le_mul hn).mp le_rfl
  simpa only [Fintype.card_fin] using HighIncidence.high_card_mul_le
    (suppliedScope n scopes) (((scopes.map List.length).sum * t) ⌈/⌉ n) t (by simpa using hb)

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CostAssemblyHighMask
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Guard success for the actual forward mask computed from all supplied raw
scopes.  The high cutoff counts raw entries, including harmless overcounts. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open LeafStatisticsProgram LeafStatisticsSemantics HighIncidenceProgram

private theorem scanSum_ones_eq_count (mask : List Bool) (v : ℕ) :
    scanSum (fun _ => 1) v mask = mask.count false := by
  induction mask generalizing v with
  | nil => simp
  | cons b bs ih => cases b <;> simp [scanSum_cons, ih, Nat.add_comm]

theorem measured_free_eq_false_count (scopes : List (List ℕ)) (mask : List Bool) :
    (measured scopes mask).free = mask.count false := by
  simp only [measured, totals_free, LeafStatisticsSemantics.zero, Nat.zero_add]
  exact scanSum_ones_eq_count mask 0

private theorem count_bool_partition (mask : List Bool) :
    mask.count false + mask.count true = mask.length := by
  induction mask with
  | nil => simp
  | cons b bs ih => cases b <;> simp [] <;> omega

theorem measured_highPrefix_free (scopes : List (List ℕ)) (cut n : ℕ) :
    (measured scopes (highPrefix scopes cut n).reverse).free =
      n - Branches.trueCount (highPrefix scopes cut n) := by
  rw [measured_free_eq_false_count, List.count_reverse]
  have hc := count_bool_partition (highPrefix scopes cut n)
  have hl := highPrefix_length scopes cut n
  have ht := Subexp.PaddedCompletion.trueCount_eq_count (highPrefix scopes cut n)
  change Branches.trueCount (highPrefix scopes cut n) =
    (highPrefix scopes cut n).count true at ht
  omega

theorem forwardHighMask_length (scopes : List (List ℕ)) (n τ : ℕ) :
    (forwardHighMask scopes n τ).length = n := by
  simp [forwardHighMask]

theorem forwardHighMask_retains_half (scopes : List (List ℕ)) (n τ : ℕ)
    (hn : 0 < n) (hτ : 2 ≤ τ) :
    n ≤ 2*(measured scopes (forwardHighMask scopes n τ)).free := by
  have hpos : 0 < τ := by omega
  have h := computed_high_dimension_rawMass scopes n τ hn hpos
  have hm := (Nat.le_div_iff_mul_le hpos).mp h
  have ht := Nat.mul_le_mul_left
    (Branches.trueCount (highPrefix scopes (((scopes.map List.length).sum * τ) ⌈/⌉ n) n)) hτ
  have he := measured_highPrefix_free scopes (((scopes.map List.length).sum * τ) ⌈/⌉ n) n
  change (measured scopes (forwardHighMask scopes n τ)).free = _ at he
  omega

theorem highThreshold_ge_two (n : ℕ) : 2 ≤ Nat.sqrt (Asymptotic.L n)+1 := by
  have h := Nat.sqrt_pos.mpr (Asymptotic.L_pos n)
  omega

/-- The large-input cutoff is uniform in every raw scope family and mark.
Only their explicit polylogarithmic upper resource bounds are supplied by
the caller; half-retention and all nondegeneracy guards are derived here. -/
theorem eventually_forwardHighMask_guards_oai (C q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (scopes : List (List ℕ)) (clauses width : ℕ),
      let mask := forwardHighMask scopes n (Nat.sqrt (Asymptotic.L n)+1)
      0 < clauses → (∀ row ∈ scopes, row.Nodup) →
      (measured scopes mask).occurrence ≤ C*Asymptotic.L n^q →
      measuredArity scopes mask ≤ C*Asymptotic.L n^q →
      LeafParametersProgram.Guard (measuredParameterInput scopes mask clauses width) := by
  filter_upwards [eventually_measured_guards C q, eventually_ge_atTop (1 : ℕ)]
    with n hn hnpos scopes clauses width
  dsimp only
  intro hcl hnodup hB ha
  exact hn scopes _ clauses width (forwardHighMask_length _ _ _)
    (forwardHighMask_retains_half _ _ _ (by omega) (highThreshold_ge_two n))
    hcl hnodup hB ha

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_forwardHighMask_guards_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_forwardHighMask_guards_oai
