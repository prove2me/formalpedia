-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_scan_bounds_of_scope_resources
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:02:11.398997+00:00
-- url     : https://prove2.me/submissions/1ae123da-ff5a-4206-ada3-95fee65fe644

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_eventually_raw_scope_guards

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNF
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable list operations for CNF formulas

These definitions use explicit finite lists and decidable literal comparisons.
The structural bounds count list elements or comparison invocations; they make
no assumption that an arbitrary `DecidableEq` comparison has unit bit cost.
-/

namespace SubexponentialSAT.ExecCNF

universe u

variable {α : Type u} [DecidableEq α]

theorem dedupLiterals_nodup (C : Clause α) : (dedupLiterals C).Nodup := by
  induction C with
  | nil => simp [dedupLiterals]
  | cons x xs ih =>
    by_cases h : contains x xs = true
    · simpa [dedupLiterals, h] using ih
    · simp only [dedupLiterals, ite_eq_right h, List.nodup_cons]
      exact ⟨fun hm => h ((contains_true x xs).mpr ((mem_dedupLiterals x xs).mp hm)), ih⟩

end SubexponentialSAT.ExecCNF

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecSunflowerSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit finite sunflower search, with counted list scans. -/
namespace SubexponentialSAT.ExecSunflowerSearch

open ExecCNF
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

@[simp] theorem dedupLiterals_length (C : Clause α) :
    (dedupLiterals C).length = (clauseSet C).card := by
  have h := List.toFinset_card_of_nodup (dedupLiterals_nodup C)
  change (clauseSet (dedupLiterals C)).card = _ at h
  rw [clauseSet_dedupLiterals] at h
  exact h.symm

end SubexponentialSAT.ExecSunflowerSearch

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
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

theorem highBranchCount_le_sqrt (scopes : List (List ℕ)) (n : ℕ) (hn : 0 < n) :
    (Branches.trueCount (highPrefix scopes
      (((scopes.map List.length).sum*(Nat.sqrt (Asymptotic.L n)+1)) ⌈/⌉ n) n) : ℝ) ≤
      (n : ℝ) / Real.sqrt (Asymptotic.L n : ℝ) := by
  let τ := Nat.sqrt (Asymptotic.L n)+1
  let H := Branches.trueCount (highPrefix scopes
    (((scopes.map List.length).sum*τ) ⌈/⌉ n) n)
  have hτ : 0 < τ := by dsimp [τ]; omega
  have hcount : H*τ ≤ n :=
    (Nat.le_div_iff_mul_le hτ).mp (computed_high_dimension_rawMass scopes n τ hn hτ)
  have hroot : Real.sqrt (Asymptotic.L n : ℝ) ≤ (τ : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hs : Asymptotic.L n ≤ τ^2 := (Nat.lt_succ_sqrt' (Asymptotic.L n)).le
    exact_mod_cast hs
  have hpos : 0 < Real.sqrt (Asymptotic.L n : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Asymptotic.L_pos n)
  have hc : (H : ℝ)*(τ : ℝ) ≤ n := by exact_mod_cast hcount
  change (H : ℝ) ≤ (n : ℝ) / Real.sqrt (Asymptotic.L n : ℝ)
  apply (le_div_iff₀ hpos).mpr
  exact (mul_le_mul_of_nonneg_left hroot (by positivity : (0 : ℝ) ≤ H)).trans hc

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeProducer
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Construct a clause's local chunk scope from its encoded literals

This fixed program maps actual literal records to chunk records, restores the
record order, and invokes the checked stable deduplicator. Its output order is
the last-occurrence order used by the materializer and incidence-plan producer.
-/

namespace SubexponentialSAT.SubexpScopeProducer

open BitProgram StructuredCalls SubexpChunkRecordMap

theorem scope_nodup (ell : List Bool) (codes : List ℕ) : (scope ell codes).Nodup :=
  ExecCNF.dedupLiterals_nodup _

end SubexponentialSAT.SubexpScopeProducer

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw hash scopes include every referenced literal, irrespective of its
coefficient. The physical materializer preserves these exact original codes. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram

theorem scope_nodup (terms : List Term) : (scope terms).Nodup :=
  SubexpScopeProducer.scope_nodup _ _

end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafScopeResourceBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Resource bounds for the exact physical scope stream, including zero
coefficients, repeated raw slots, empty hash rows, and the optional mark. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open HashScopeProgram

theorem scopes_nodup (t d : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (rows : RawTable.Rows clauses.length)
    (mark : Option (Fin clauses.length)) :
    ∀ row ∈ Complete.scopes t d codes rows mark, row.Nodup := by
  intro row hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr
    exact scope_nodup _
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact SubexpScopeProducer.scope_nodup _ _

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

/-- The physically loaded parameter input is exactly the neutral-completed
statistics input used by the uniform guard theorem. -/
theorem Query.input_eq_measured (q : Query) (k : ℕ)
    (hm : BinaryArithmetic.toNat q.modulus=q.clauses.length) :
    q.input k=CostAssembly.measuredParameterInput q.scopeRows q.forward q.clauses.length k := by
  unfold Query.input numericInput CostAssembly.measuredParameterInput
  simp only [Query.forward_length,hm]
  rfl

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryParameterBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform input-polynomial numeric caps for every actually produced query.
These bounds quantify over every physical padding, while physical word-length
bounds are supplied separately by the concrete producers. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open Filter SqrtLog SqrtLog.Asymptotic SqrtLog.ProducedQueryResources
  SqrtLog.LeafQueryFrontend SqrtLog.LeafScopeResourceBounds in
/-- Actual raw scope resources imply the sharp scan bounds for every marked
or unmarked query, without an identity with the old selector history. -/
theorem eventually_scan_bounds_of_scope_resources_oai (k qi : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : Query) (B : ℕ), q.Valid → ambient q = n →
      0 < q.clauses.length → q.clauses.length ≤ n * B → B ≤ L n ^ qi →
      q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 →
      HighIncidenceProgram.Prepare.mass q.scopeRows ≤
        (3 * n * SparseCode.degreeBound q.clauses.length B +
          (HashSelect.loopCap n q.clauses.length + 1) *
            SparseCode.distanceDenom q.clauses.length B + 1) * k →
      (∀ row ∈ q.scopeRows, row.length ≤
        (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k) →
      ScanBounds q k (resourceExponent qi + 1) := by
  filter_upwards [eventually_raw_scope_guards k qi] with n hg q B hv hn hm hmb hB hlen hmass har
  have hforward : q.forward = CostAssembly.forwardHighMask q.scopeRows n (Nat.sqrt (L n) + 1) := by
    dsimp [ambient] at hn
    simp only [Query.forward, highMask, CostAssembly.forwardHighMask,
      EarlyThreshold.threshold, HighIncidenceProgram.Prepare.mass, hn]
  have hinput := q.input_eq_measured k hv.2.2.2.2.2.1
  rw [hforward] at hinput
  obtain ⟨hguard,hfree,hhalf,hfactors,hocc,harity⟩ :=
    hg q.scopeRows q.clauses.length B hm hmb hB hlen hmass har
      (scopes_nodup 1 0 q.codes q.rows q.mark)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hinput] using hguard
  · simpa only [hinput, hn] using And.intro hfree hhalf
  · simpa only [hinput, hn] using hfactors
  · simpa only [hinput] using hocc
  · simpa only [hinput] using harity
  · exact CostAssembly.highBranchCount_le_sqrt q.scopeRows (ambient q) hv.2.1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_scan_bounds_of_scope_resources_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_scan_bounds_of_scope_resources_oai
