-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_envelope
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:36:45.094346+00:00
-- url     : https://prove2.me/submissions/8c6bd86b-674b-45a3-a461-d12fdf6bf87c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S178
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HashGreedyCode_supplied_history_raw_resources
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryEnvelopeBudgets_chosen_ofPacking_cutoff

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_DyadicWidth
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A positive dyadic width for bounded tuple enumeration, including zero. -/

namespace SubexponentialSAT.DyadicWidth

theorem width_pos (m : ℕ) : 0 < width m := by
  unfold width
  omega

theorem lt_two_pow_width (m : ℕ) : m < 2 ^ width m :=
  Nat.lt_pow_succ_log_self (by decide) m

end SubexponentialSAT.DyadicWidth

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Encoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An explicit binary encoding of finite CNF formulas

Numeric fields are unary on the binary alphabet: `n` is `n` true bits and
one false bit. Lists use an explicit escape frame, and both levels of finite
sets are sorted before encoding. No enumeration of semantic truth values or
noncomputable choice participates in the encoding.
-/

namespace SubexponentialSAT.Encoding

theorem literalCode_lt {n : ℕ} (l : SAT.Literal (Fin n)) : literalCode l < 2 * n := by
  have hv := l.variable.isLt
  cases hp : l.positive <;> simp [literalCode, hp] ; omega

end SubexponentialSAT.Encoding

end OAI.Algorithms
end

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

theorem dedupLiterals_length_le (C : Clause α) : (dedupLiterals C).length ≤ C.length := by
  induction C with
  | nil => simp [dedupLiterals]
  | cons x xs ih =>
    by_cases h : contains x xs = true
    · simpa [dedupLiterals, h] using ih.trans (Nat.le_succ _)
    · simpa [dedupLiterals, h] using Nat.succ_le_succ ih

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecSparsifyEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact syntax and normalization bridges for the word-based node search. -/

namespace SubexponentialSAT.ExecSparsifyEncoding

open ExecCNF ExecSunflowerCodeTransport

theorem encodeList_map {α β : Type*} (f : α → β) (enc : β → List Bool) (xs : List α) :
    Encoding.encodeList enc (xs.map f) = Encoding.encodeList (fun x => enc (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Encoding.encodeList, ih]

end SubexponentialSAT.ExecSparsifyEncoding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidates
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
The hash stream visits binary payloads in increasing unsigned order and reduces
each indexed ternary digit modulo3*m before the existing row assembler. Every
original candidate is attained and unchanged by normalization. Extra normalized
duplicates preserve the minimum. Visits are bounded by the square of the old family.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamily

theorem digitWidth_sufficient (m : ℕ) : 3 * m ≤ 2 ^ digitWidth m :=
  (DyadicWidth.lt_two_pow_width _).le


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

theorem degree_le (m B : ℕ) : degree m B ≤ m := min_le_left _ _

theorem eight_mul_le_degreeBound (m : ℕ) {B : ℕ} (hB : 0 < B) :
    8 * B ≤ degreeBound m B := by
  have hL : 1 ≤ logSize m := logSize_pos m
  have hq : B ≤ gapDenom m B := by unfold gapDenom; nlinarith
  have hqpos := gapDenom_pos m hB
  have hsq : gapDenom m B ≤ gapDenom m B ^ 2 := by nlinarith
  unfold degreeBound
  nlinarith

theorem dimensionFor_le (m : ℕ) {D r : ℕ} (hD : 0 < D)
    (hr : m ≤ D * 2 ^ r) : dimensionFor m D ≤ r := by
  simp only [dimensionFor, dite_eq_left hD]
  exact Nat.find_min' (exists_dimension m hD) hr

theorem dimensionFor_min (m : ℕ) {D r : ℕ} (hD : 0 < D)
    (hr : r < dimensionFor m D) : D * 2 ^ r < m := by
  simp only [dimensionFor, dite_eq_left hD] at hr
  exact Nat.lt_of_not_ge (Nat.find_min (exists_dimension m hD) hr)

theorem dimensionFor_self {m : ℕ} (hm : 0 < m) : dimensionFor m m = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact dimensionFor_le m hm (by simp)

theorem dimensionFor_edge_upper {m D : ℕ} (hm : 0 < m) (hD : 0 < D) (hDm : D ≤ m) :
    D * 2 ^ dimensionFor m D < 2 * m := by
  cases hr : dimensionFor m D with
  | zero => simp only [pow_zero, mul_one]; omega
  | succ r =>
    have hprev : D * 2 ^ r < m := dimensionFor_min m hD (by omega)
    simp only [pow_succ]
    nlinarith

theorem graph_edge_upper {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    2 ^ dimension m B * degree m B < 2 * m := by
  simpa [dimension, Nat.mul_comm] using
    dimensionFor_edge_upper hm (degree_pos hm hB) (degree_le m B)

theorem dimension_zero_of_small {m B : ℕ} (hm : 0 < m)
    (h : m ≤ degreeBound m B) : dimension m B = 0 := by
  simp [dimension, degree, min_eq_left h, dimensionFor_self hm]

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SparseCodeBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

theorem localRows_upper (m B : ℕ) :
    8 * B * localRows m B ≤ degree m B + 8 * B := by
  have hh := Nat.div_mul_le_self (degree m B) (8 * B)
  unfold localRows
  nlinarith

theorem totalRows_le {n m B : ℕ} (hn : 0 < n) (hm : 0 < m) (hB : 0 < B)
    (hmb : m ≤ n * B) : totalRows m B ≤ 3 * n := by
  by_cases hlarge : degreeBound m B ≤ m
  · have hd : degree m B = degreeBound m B := min_eq_right hlarge
    have hbudget : 4 * B * localRows m B ≤ degree m B := by
      have htop := localRows_upper m B
      have hbig := eight_mul_le_degreeBound m hB
      rw [← hd] at hbig
      nlinarith
    have hedge := graph_edge_upper hm hB
    have hrows : totalRows m B * (2 * B) < n * (2 * B) := by
      calc
        _ = 2 ^ dimension m B * (4 * B * localRows m B) := by
          unfold totalRows
          ring
        _ ≤ 2 ^ dimension m B * degree m B := Nat.mul_le_mul_left _ hbudget
        _ < 2 * m := hedge
        _ ≤ n * (2 * B) := by nlinarith
    have : totalRows m B < n := Nat.lt_of_mul_lt_mul_right hrows
    omega
  · have hd : degree m B = m := min_eq_left (by omega)
    have hr : dimension m B = 0 := dimension_zero_of_small hm (by omega)
    have htop := localRows_upper m B
    rw [hd] at htop
    have hh : (8 * localRows m B) * B ≤ (n + 8) * B := by nlinarith
    have hrows : 8 * localRows m B ≤ n + 8 :=
      le_of_mul_le_mul_right hh hB
    simp only [totalRows, hr, pow_zero, mul_one]
    omega

end SubexponentialSAT.SqrtLog.SparseCode

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

theorem scope_length_le (ell : List Bool) (codes : List ℕ) :
    (scope ell codes).length ≤ codes.length := by
  exact (ExecCNF.dedupLiterals_length_le _).trans_eq (List.length_map ..)

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

theorem mergedCodes_length (terms : List Term) :
    (mergedCodes terms).length = (terms.map fun term => term.2.length).sum := by
  simp [mergedCodes, List.length_flatMap, List.map_reverse]

theorem scope_length_le (terms : List Term) :
    (scope terms).length ≤ (terms.map fun term => term.2.length).sum := by
  exact (SubexpScopeProducer.scope_length_le _ _).trans_eq (mergedCodes_length terms)

end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramNativeSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact scopes of the physically stored sparse raw rows and optional original
marked clause. These definitions are shared by the machine and resource proofs. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram
namespace FromTuple


theorem mem_interpreted_scope (t d : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ)
    (terms : List (Fin clauses.length × ZMod 3)) (v : ℕ) :
    v ∈ scope (interpretedTerms (clauses := clauses) t d codes terms) ↔
      ∃ a∈terms, ∃ c∈codes a.1, c/2=v := by
  rw [mem_scope]
  constructor
  · rintro ⟨term,hterm,c,hc,hv⟩
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hterm
    exact ⟨a,ha,c,hc,hv⟩
  · rintro ⟨a,ha,c,hc,hv⟩
    exact ⟨_,List.mem_map.mpr ⟨a,ha,rfl⟩,c,hc,hv⟩

end FromTuple
namespace Complete

theorem scopes_length (t d : ℕ) {clauses : List (List Bool)} (codes : Fin clauses.length → List ℕ)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) :
    (scopes (clauses := clauses) t d codes rows mark).length=rows.length+mark.isSome.toNat := by
  cases mark <;> simp [scopes]

end Complete
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

theorem slots_le {α : Type*} (rows : List (List α)) (D : ℕ)
    (h : ∀ row ∈ rows, row.length ≤ D) : slots rows ≤ rows.length * D := by
  induction rows with
  | nil => simp [slots]
  | cons row rows ih =>
    have hr := h row (by simp)
    have hs := ih (fun r hr => h r (by simp [hr]))
    simp only [slots, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul] at *
    omega

theorem row_length (t d k : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (hcodes : ∀ i, (codes i).length ≤ k)
    (row : List (Fin clauses.length × ZMod 3)) :
    (scope (FromTuple.interpretedTerms t d codes row)).length ≤ row.length * k := by
  apply (scope_length_le _).trans
  simpa [slots, FromTuple.interpretedTerms, List.map_map, Function.comp_def] using
    slots_le (row.map fun a => codes a.1) k (by
      intro r hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact hcodes a.1)

theorem mark_length (k : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (hcodes : ∀ i, (codes i).length ≤ k)
    (i : Fin clauses.length) : (Marked.markedScope (codes i)).length ≤ k :=
  (SubexpScopeProducer.scope_length_le _ _).trans (hcodes i)

theorem scope_mass (t d k : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (hcodes : ∀ i, (codes i).length ≤ k)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) :
    slots (Complete.scopes t d codes rows mark) ≤ (slots rows + mark.isSome.toNat) * k := by
  have hr : slots (rows.map fun row => scope (FromTuple.interpretedTerms t d codes row)) ≤ slots rows * k := by
    induction rows with
    | nil => simp [slots]
    | cons row rows ih =>
      have hh := row_length t d k codes hcodes row
      simp only [slots, List.map_cons, List.sum_cons, Nat.add_mul] at *
      omega
  cases mark with
  | none => simpa [Complete.scopes, slots] using hr
  | some i =>
    have hm := mark_length k codes hcodes i
    simp only [Complete.scopes, Option.toList_some, List.map_cons, List.map_nil,
      slots, List.map_append, List.sum_append, List.sum_cons, List.sum_nil,
      Nat.add_zero, Option.isSome_some, Bool.toNat_true, Nat.add_mul, Nat.one_mul] at *
    omega

theorem scope_arity (t d k D : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (hcodes : ∀ i, (codes i).length ≤ k)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length))
    (hrows : ∀ row ∈ rows, row.length ≤ D) (hD : 1 ≤ D) :
    ∀ row ∈ Complete.scopes t d codes rows mark, row.length ≤ D * k := by
  intro row hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨r, hrmem, rfl⟩ := List.mem_map.mp hr
    exact (row_length t d k codes hcodes r).trans (Nat.mul_le_mul_right k (hrows r hrmem))
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact (mark_length k codes hcodes i).trans (by simpa using Nat.mul_le_mul_right k hD)

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The leaf's serialized raw clauses and the selector's indexed clauses
have exactly the same ambient models. Repeated clauses or literals are not
assigned extra model multiplicity. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics

open SqrtLog DisjointReuse
open scoped BigOperators

theorem recordCodes_word {n : ℕ} (F : RawCNF n)
    (i : Fin (NativeTerminal.clauseRecords F).length) :
    (NativeTerminal.clauseRecords F)[i.val] =
      Encoding.encodeList Encoding.encodeNat (recordCodes F i) := by
  simp only [NativeTerminal.clauseRecords, List.getElem_map, recordCodes,
    List.get_eq_getElem, recordIndex, ExecSparsifyEncoding.encodeList_map]
  rfl

theorem recordCodes_lt {n : ℕ} (F : RawCNF n)
    (i : Fin (NativeTerminal.clauseRecords F).length) :
    ∀ v ∈ recordCodes F i, v < 2 * n := by
  intro v hv
  obtain ⟨lit,_hmem,rfl⟩ := List.mem_map.mp hv
  exact Encoding.literalCode_lt lit

theorem recordCodes_length {n k : ℕ} (F : RawCNF n)
    (hv : DisjointReuse.SparseDFSRefinement.Valid k F)
    (i : Fin (NativeTerminal.clauseRecords F).length) :
    (recordCodes F i).length ≤ k := by
  simp only [recordCodes, List.length_map]
  exact hv.width _ (List.get_mem F (recordIndex F i))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighFrontendSources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Typed source and empty-workspace relations follow from the actual trial
and accepted source stages. Changing the marked clause does not change the
immutable source words; its scope and high mask are recomputed by the frontend. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendSources

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open HighMarkedFrontend

/-- Every current hashed or marked scope comes from an actual source literal.
This applies uniformly to the optional mark; no precomputed scope bound is an
input to the machine. -/
theorem scopeRows_lt (q : LeafQueryFrontend.Query) (n : ℕ)
    (hc : ∀ i, ∀ c ∈ q.codes i, c < 2*n) :
    ∀ row ∈ q.scopeRows, ∀ v ∈ row, v < n := by
  intro row hr v hv
  change row ∈ (q.rows.map (fun terms => HashScopeProgram.scope
    (HashScopeProgram.FromTuple.interpretedTerms (clauses := q.clauses) 1 0 q.codes terms)) ++
      q.mark.toList.map (fun i => HashScopeProgram.Marked.markedScope (q.codes i))) at hr
  rcases List.mem_append.mp hr with hh | hm
  · obtain ⟨terms,_ht,rfl⟩ := List.mem_map.mp hh
    obtain ⟨term,_hm,c,hc',rfl⟩ :=
      (HashScopeProgram.FromTuple.mem_interpreted_scope 1 0 q.codes terms v).mp hv
    exact (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr
      (by simpa only [Nat.mul_comm] using hc term.1 c hc')
  · obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hm
    obtain ⟨c,hc',he⟩ := (SubexpScopeProducer.mem_scope [true] (q.codes i) v).mp hv
    have he' : c/2=v := by simpa [BinaryArithmetic.toNat,BinaryArithmetic.bitVal] using he
    rw [← he']
    exact (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr
      (by simpa only [Nat.mul_comm] using hc i c hc')

theorem rawQuery_clauses {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows (NativeTerminal.clauseRecords F).length)
    (mark : Option (Fin (NativeTerminal.clauseRecords F).length))
    (index width modulus ambient : List Bool) :
    ∀ i, (rawQuery F rows mark index width modulus ambient).clauses[i.val]=
      Encoding.encodeList Encoding.encodeNat
        ((rawQuery F rows mark index width modulus ambient).codes i) :=
  NativeLeafSemantics.recordCodes_word F

theorem rawQuery_scopeRows {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows (NativeTerminal.clauseRecords F).length)
    (mark : Option (Fin (NativeTerminal.clauseRecords F).length))
    (index width modulus ambient : List Bool) (hn : BinaryArithmetic.toNat ambient=n) :
    ∀ row ∈ (rawQuery F rows mark index width modulus ambient).scopeRows,
      ∀ v ∈ row, v < BinaryArithmetic.toNat ambient := by
  rw [hn]
  exact scopeRows_lt _ n (NativeLeafSemantics.recordCodes_lt F)

theorem recordMark_index {n : ℕ} (F : DisjointReuse.RawCNF n)
    (mark : Option (Fin F.length)) (index : List Bool)
    (hi : ∀ i, mark=some i → index=Encoding.encodeNat i.val) :
    ∀ i, recordMark F mark=some i → index=Encoding.encodeNat i.val := by
  intro i h
  obtain ⟨j,hj,hji⟩ := Option.map_eq_some_iff.mp h
  subst i
  exact hi j hj

/-- Concrete raw records satisfy every source-side frontend validity field.
The positive ambient case is selected by the actual terminal dispatcher. -/
theorem rawQuery_valid {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows (NativeTerminal.clauseRecords F).length)
    (mark : Option (Fin (NativeTerminal.clauseRecords F).length))
    (index width modulus ambient : List Bool)
    (hn : 0<n) (hw : 0<width.length) (hsize : 3*F.length≤2^width.length)
    (hi : ∀ i, mark=some i → index=Encoding.encodeNat i.val)
    (hm : BinaryArithmetic.toNat modulus=F.length)
    (ha : BinaryArithmetic.toNat ambient=n) :
    (rawQuery F rows mark index width modulus ambient).Valid := by
  refine ⟨hw,?_,rawQuery_clauses F rows mark index width modulus ambient,
    ?_,hi,?_,rawQuery_scopeRows F rows mark index width modulus ambient ha⟩
  · simpa only [rawQuery,ha] using hn
  · simpa only [rawQuery,NativeTerminal.clauseRecords,List.length_map] using hsize
  · simpa only [rawQuery,NativeTerminal.clauseRecords,List.length_map] using hm

theorem rawQueryFromRows_valid {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) (mark : Option (Fin F.length))
    (index width modulus ambient : List Bool)
    (hn : 0<n) (hw : 0<width.length) (hsize : 3*F.length≤2^width.length)
    (hi : ∀ i, mark=some i → index=Encoding.encodeNat i.val)
    (hm : BinaryArithmetic.toNat modulus=F.length)
    (ha : BinaryArithmetic.toNat ambient=n) :
    (rawQueryFromRows F rows mark index width modulus ambient).Valid :=
  rawQuery_valid F _ _ index width modulus ambient hn hw hsize
    (recordMark_index F mark index hi) hm ha

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendSources
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashQueryResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete scope resources of the actual serialized raw-formula query.
The dependent clause-index cast preserves every repeated or zero raw slot;
these results use no identity with the former materialized selector. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryResources

open SqrtLog HighFrontendSources HashGreedyCode
open DisjointReuse

theorem recordRows_arity {n : ℕ} (F : RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) (D : ℕ)
    (hrows : ∀ row ∈ rows, row.length ≤ D) :
    ∀ row ∈ recordRows F rows, row.length ≤ D := by
  intro row hrow
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
  simpa only [List.length_map] using hrows r hr

/-- The frontend's literal scopeRows has the resource bounds of the actual
raw rows and actual raw clause widths. The optional mark contributes at most
one clause; each produced variable scope is duplicate-free. -/
theorem rawQuery_resources {n k : ℕ} (F : RawCNF n)
    (hv : SparseDFSRefinement.Valid k F) (rows : HashScopeProgram.RawTable.Rows F.length)
    (mark : Option (Fin F.length)) (index width modulus ambient : List Bool)
    (R M D : ℕ) (hR : rows.length ≤ R) (hM : LeafScopeResourceBounds.slots rows ≤ M)
    (hD : 1 ≤ D) (hrows : ∀ row ∈ rows, row.length ≤ D) :
    let q := rawQueryFromRows F rows mark index width modulus ambient
    q.scopeRows.length ≤ R + 1 ∧ LeafScopeResourceBounds.slots q.scopeRows ≤ (M + 1) * k ∧
      (∀ row ∈ q.scopeRows, row.length ≤ D * k) ∧ (∀ row ∈ q.scopeRows, row.Nodup) := by
  dsimp only [rawQueryFromRows, rawQuery, LeafQueryFrontend.Query.scopeRows]
  have hcodes := NativeLeafSemantics.recordCodes_length F hv
  have hmark : (recordMark F mark).isSome.toNat ≤ 1 := by cases mark <;> simp [recordMark]
  refine ⟨?_, ?_, ?_, LeafScopeResourceBounds.scopes_nodup 1 0 _ _ _⟩
  · rw [HashScopeProgram.Complete.scopes_length, recordRows_length]
    omega
  · apply (LeafScopeResourceBounds.scope_mass 1 0 k _ hcodes _ _).trans
    rw [recordRows_slots]
    exact Nat.mul_le_mul_right k (by omega)
  · exact LeafScopeResourceBounds.scope_arity 1 0 k D _ hcodes _ _
      (recordRows_arity F rows D hrows) hD

/-- Every attained selected history, including the final unmarked query,
uses the concrete query record and the exact indexed raw formula. -/
theorem history_resources {n k B : ℕ} (F : RawCNF n)
    (hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (rounds : ℕ) (mark : Option (Fin F.length)) (index width modulus ambient : List Bool) :
    let m := F.length
    let rows := (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
      (SparseCode.distanceDenom m B) (initial shifts Q) rounds).map (raw m hm)
    let q := rawQueryFromRows F rows mark index width modulus ambient
    q.scopeRows.length ≤ SparseCode.totalRows m B + rounds + 1 ∧
      LeafScopeResourceBounds.slots q.scopeRows ≤
        (SparseCode.totalRows m B * SparseCode.degreeBound m B +
          rounds * SparseCode.distanceDenom m B + 1) * k ∧
      (∀ row ∈ q.scopeRows, row.length ≤
        (SparseCode.degreeBound m B + SparseCode.distanceDenom m B + 1) * k) ∧
      (∀ row ∈ q.scopeRows, row.Nodup) := by
  dsimp only
  obtain ⟨hR, hM, hrows⟩ := supplied_history_raw_resources (NativeLeafSemantics.indexed F) hm shifts Q rounds
  exact rawQuery_resources F hv _ mark index width modulus ambient _ _ _ hR.le hM (by omega) hrows

/-- Exact guard-resource envelope for the actual final or intermediate
selected-history query. Positivity is used only for the produced-code row
bound; no guard, layout, or evaluator is supplied. -/
theorem history_uniform_resources {n k B : ℕ} (F : RawCNF n)
    (hv : SparseDFSRefinement.Valid k F) (hn : 0 < n) (hm : 0 < F.length)
    (hB : 0 < B) (hmb : F.length ≤ n * B)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (rounds : ℕ) (hrounds : rounds ≤ HashSelect.loopCap n F.length)
    (mark : Option (Fin F.length)) (index width modulus ambient : List Bool) :
    let m := F.length
    let rows := (HashGreedyCNF.history (NativeLeafSemantics.indexed F)
      (SparseCode.distanceDenom m B) (initial shifts Q) rounds).map (raw m hm)
    let q := rawQueryFromRows F rows mark index width modulus ambient
    q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n m + 2 ∧
      HighIncidenceProgram.Prepare.mass q.scopeRows ≤
        (3 * n * SparseCode.degreeBound m B +
          (HashSelect.loopCap n m + 1) * SparseCode.distanceDenom m B + 1) * k ∧
      (∀ row ∈ q.scopeRows, row.length ≤
        (SparseCode.degreeBound m B + SparseCode.distanceDenom m B + 1) * k) ∧
      (∀ row ∈ q.scopeRows, row.Nodup) := by
  dsimp only
  obtain ⟨hr, hmss, har, hnd⟩ := history_resources F hv hm shifts Q rounds mark index width modulus ambient
  have htotal := SparseCode.totalRows_le hn hm hB hmb
  have hslots := Nat.mul_le_mul_right (SparseCode.degreeBound F.length B) htotal
  have hnew := Nat.mul_le_mul_right (SparseCode.distanceDenom F.length B)
    (show rounds ≤ HashSelect.loopCap n F.length + 1 by omega)
  exact ⟨by omega, hmss.trans (Nat.mul_le_mul_right k (by omega)), har, hnd⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryResources
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashQueryParameterBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual trial and accepted queries inherit the width-fixed scalar caps.
Every generic validity and raw-scope premise is discharged from the literal
formula, produced code rows, attained history and physical master words. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds

open BitProgram StructuredCalls SqrtLog DisjointReuse HighFrontendSources
open HashGreedyCode HashQueryEntry ProducedQueryResources


open CostAssembly MulticolorTypes

/-- The same literal accepted query and actual complete output alphabet
inherit the original resource envelope. All constants and the cutoff precede
the formula, attained history, candidate, mark and physical parameter words. -/
theorem accepted_envelope_oai (k C d e power ordinaryPower : ℕ) (hk : 2 ≤ k) :
    ∃ cutoff : ℕ, ∀ n ≥ cutoff,
      let B := 4 * SparseBudget.chooseM k 1 (sparsifySchedule n) (by omega) ^ (k - 1)
      ∀ (F : RawCNF n) (_hv : SparseDFSRefinement.Valid k F) (hm : 0 < F.length),
        F.length ≤ n * B →
      ∀ (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
        (rounds : ℕ), rounds ≤ HashSelect.loopCap n F.length →
      ∀ (state : State 40 896),
        (state.stacks 783).length = HashCandidates.digitWidth F.length →
        BinaryArithmetic.toNat (state.stacks 782) = F.length →
        BinaryArithmetic.toNat (state.stacks 785) = n →
      let q := acceptedQuery F hm shifts Q rounds state
      q.Valid ∧ ambient q = n ∧ ScanBounds q k (4 * k + 3) ∧ SmallInputs q k n ∧
        ∀ (hg : LeafParametersProgram.Guard (q.input k))
          (a : Word (problem q k hg).r (problem q k hg).Q)
          (tail : List (Word (problem q k hg).r (problem q k hg).Q)),
          (a :: tail).Nodup → (∀ z, z ∈ a :: tail) →
          let p := ofPacking q k B C d (2 * (k - 1) + 1) e hg a tail
          Bounds (2 * (k - 1) + 1) (4 * k + 3) (9 * e + 8) n p ∧
          (nativeEnvelope k n power ordinaryPower p : ℝ) ≤
            (18 : ℝ) ^ power * (2 : ℝ) ^
              ((1 + (power : ℝ) * exponentConstant k (4 * k + 3)) * Statement.runtimeScale n) := by
  obtain ⟨cutoff, hbound⟩ := QueryEnvelopeBudgets.chosen_ofPacking_cutoff k C d e power ordinaryPower hk
  refine ⟨max cutoff 1, ?_⟩
  intro n hn B F hv hm hmb shifts Q rounds hr state hwidth hmod hamb q
  have hnpos : 0 < n := by omega
  have hB : 0 < B := by
    dsimp only [B, SparseBudget.chooseM]
    positivity
  have hvq : q.Valid := by
    apply rawQueryFromRows_valid F _ none [false]
      (state.stacks 783) (state.stacks 782) (state.stacks 785) hnpos
    · rw [hwidth]
      exact DyadicWidth.width_pos _
    · rw [hwidth]
      exact HashCandidates.digitWidth_sufficient _
    · intro i he
      cases he
    · exact hmod
    · exact hamb
  have hqn : ambient q = n := hamb
  have hcl : q.clauses.length = F.length := by
    simp [q, acceptedQuery, rawQueryFromRows, rawQuery, NativeTerminal.clauseRecords]
  obtain ⟨hlen, hmass, harity, _hnd⟩ := HashQueryResources.history_uniform_resources F hv hnpos hm hB hmb
    shifts Q rounds hr none [false]
    (state.stacks 783) (state.stacks 782) (state.stacks 785)
  have hlen' : q.scopeRows.length ≤ 3 * n + HashSelect.loopCap n q.clauses.length + 2 := by
    rw [hcl]
    exact hlen
  have hmass' : HighIncidenceProgram.Prepare.mass q.scopeRows ≤
      (3 * n * SparseCode.degreeBound q.clauses.length B +
        (HashSelect.loopCap n q.clauses.length + 1) *
          SparseCode.distanceDenom q.clauses.length B + 1) * k := by
    rw [hcl]
    exact hmass
  have harity' : ∀ row ∈ q.scopeRows, row.length ≤
      (SparseCode.degreeBound q.clauses.length B + SparseCode.distanceDenom q.clauses.length B + 1) * k := by
    rw [hcl]
    exact harity
  exact ⟨hvq, hqn, hbound n (by omega) q hvq hqn
    (by simpa only [hcl] using hm) (by simpa only [hcl] using hmb) hlen' hmass' harity'⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_envelope_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_envelope_oai
