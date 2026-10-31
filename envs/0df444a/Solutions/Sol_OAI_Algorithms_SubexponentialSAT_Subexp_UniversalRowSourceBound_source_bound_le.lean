-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound.source_bound_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:18:22.710413+00:00
-- url     : https://prove2.me/submissions/99802c6e-1190-412e-8b60-604d5ee6106a

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpKernelControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed controller constructing the separated postfix source

The input contains literal payloads and the three nested lists of blocks,
color groups, and terms.  The controller only parses frames, copies bits,
and emits postfix tags.  It has no arithmetic callback and never builds a
Cartesian product of the inner lists.  Three unary stacks hold the pending
right-fold operators, so the emitted source has exactly the association of
`SubexpAlgorithm.momentExpression`.
-/

namespace SubexponentialSAT.SubexpKernelControl

open BitProgram StructuredCalls

theorem operators_succ (mul : Bool) (n : ℕ) :
    operators mul (n + 1) = operators mul n ++ operator mul := by
  simp [operators, List.replicate_succ', List.flatten_append]

/-! ## Fixed source-constructor control -/

/-! ## Concrete machine states and elementary traces -/

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-- The traversal count sums individual payload costs. No product of inner
list lengths occurs in the actual loop bound. -/
theorem scanCost_le_input {α : Type*} (encode : α → Word) (cost : α → ℕ)
    (xs : List α) (a b : ℕ) (hcost : ∀ x ∈ xs, cost x ≤ a * (encode x).length + b) :
    scanCost encode cost xs ≤ (a + b + 18) * (Encoding.encodeList encode xs).length := by
  induction xs with
  | nil => simp [scanCost]
  | cons x xs ih =>
      have hx := hcost x (by simp)
      have ht := ih (fun y hy => hcost y (by simp [hy]))
      simp only [scanCost, List.map_cons, List.sum_cons] at *
      rw [Encoding.length_encodeList_cons]
      nlinarith

/-! ## Forward-output service boundary -/

@[simp] theorem operators_length (mul : Bool) (n : ℕ) :
    (operators mul n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [operators_succ, List.length_append, ih]; simp [operator]; omega

theorem flattenedCode_le_scanCost {α : Type*} (encode code : α → Word) (cost : α → ℕ)
    (xs : List α) (h : ∀ x ∈ xs, (code x).length ≤ cost x) :
    ((xs.map code).flatten).length ≤ scanCost encode cost xs := by
  induction xs with
  | nil => simp [scanCost]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons, List.flatten_cons, List.length_append,
        scanCost, List.sum_cons] at *
      omega

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed nested source emitter and its actual byte-level execution bound. -/
namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word Accumulator pushWord operator operators emit bump
  state counterWord setCounter counterPort popTag unframe emitFramedLiteral emitLiteral
  emitOperator countOne drain scan scanCost)


theorem factorCost_le_input (x : Word) (f : Factor Word) :
    factorCost x f ≤ 7 * (encodeFactor f).length + (8 * x.length + 29) := by
  simp [factorCost, encodeFactor]
  omega

theorem productCost_le_input (one x : Word) (fs : List (Factor Word)) :
    productCost one x fs ≤ (8 * x.length + 60) * (Encoding.encodeList encodeFactor fs).length +
      (8 * one.length + 13) := by
  have hs := SubexpKernelControl.scanCost_le_input encodeFactor (factorCost x) fs
    7 (8 * x.length + 29) (fun f _ => factorCost_le_input x f)
  have hl := Encoding.length_encodeList_lower encodeFactor fs
  unfold productCost
  nlinarith

theorem termCost_le_input (one x : Word) (t : Term Word) :
    termCost one x t ≤ (16 * x.length + 16 * one.length + 200) * (encodeTerm t).length := by
  have hp := productCost_le_input one x t.factors
  have hl := Encoding.length_encodeList_lower encodeFactor t.factors
  unfold termCost encodeTerm
  simp only [List.length_append, Encoding.length_frame]
  nlinarith [Nat.zero_le (x.length * t.value.length), Nat.zero_le (x.length * t.inverseNode.length),
    Nat.zero_le (one.length * t.value.length), Nat.zero_le (one.length * t.inverseNode.length),
    Nat.zero_le (one.length * (Encoding.encodeList encodeFactor t.factors).length)]

theorem rowCost_le_input (zero one x : Word) (r : Row Word) :
    rowCost zero one x r ≤
      (16 * x.length + 16 * one.length + 16 * zero.length + 300) * (encodeRow r).length := by
  have hs := SubexpKernelControl.scanCost_le_input encodeTerm (termCost one x) r.terms
    (16 * x.length + 16 * one.length + 200) 0
    (fun t _ => by simpa using termCost_le_input one x t)
  have hl := Encoding.length_encodeList_lower encodeTerm r.terms
  unfold rowCost encodeRow
  simp only [List.length_append, Encoding.length_frame]
  nlinarith [Nat.zero_le (x.length * r.delta.length), Nat.zero_le (one.length * r.delta.length),
    Nat.zero_le (zero.length * r.delta.length),
    Nat.zero_le (zero.length * (Encoding.encodeList encodeTerm r.terms).length)]

theorem factorCode_length_le (x : Word) (f : Factor Word) :
    (factorCode x f).length ≤ factorCost x f := by
  simp [factorCode, factorCost, operator, SubexpKernelControl.pushWord_length]
  omega

theorem productCode_length_le (one x : Word) (fs : List (Factor Word)) :
    (productCode one x fs).length ≤ productCost one x fs := by
  have h := SubexpKernelControl.flattenedCode_le_scanCost encodeFactor (factorCode x)
    (factorCost x) fs (fun f _ => factorCode_length_le x f)
  simp only [productCode, List.length_append, SubexpKernelControl.pushWord_length,
    SubexpKernelControl.operators_length, productCost]
  omega

theorem termCode_length_le (one x : Word) (t : Term Word) :
    (termCode one x t).length ≤ termCost one x t := by
  have hp := productCode_length_le one x t.factors
  simp only [termCode, List.length_append, SubexpKernelControl.pushWord_length,
    operator, List.length_cons, List.length_nil, termCost]
  omega

theorem rowCode_length_le (zero one x : Word) (r : Row Word) :
    (rowCode zero one x r).length ≤ rowCost zero one x r := by
  have h := SubexpKernelControl.flattenedCode_le_scanCost encodeTerm (termCode one x)
    (termCost one x) r.terms (fun t _ => termCode_length_le one x t)
  simp only [rowCode, List.length_append, SubexpKernelControl.pushWord_length,
    SubexpKernelControl.operators_length, operator, List.length_cons, List.length_nil, rowCost]
  omega

theorem rowCost_quadratic (zero one : Word) (r : Row Word) :
    rowCost zero one (zero ++ one) r ≤ 300 * inputSize zero one r ^ 2 := by
  have h := rowCost_le_input zero one (zero ++ one) r
  simp only [List.length_append] at h
  have hc : 16 * (zero.length + one.length) + 16 * one.length + 16 * zero.length + 300 ≤
      300 * inputSize zero one r := by unfold inputSize; omega
  have hl : (encodeRow r).length ≤ inputSize zero one r := by unfold inputSize; omega
  have hm := Nat.mul_le_mul hc hl
  nlinarith

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowSourceBound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial bounds for the actual nested row-data and source emitters. -/

namespace SubexponentialSAT.Subexp.UniversalRowSourceBound

open UniversalRowProgram
open UniversalRowFactorLoop (indexWord)

theorem getD_length_le (xs : List Word) (S : ℕ)
    (h : ∀ x ∈ xs, x.length ≤ S) (i : ℕ) : (xs.getD i []).length ≤ S := by
  by_cases hi : i < xs.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

theorem record_budget_le (cost : Word → ℕ) (records : List Word) (S C : ℕ)
    (hsize : ∀ w ∈ records, w.length ≤ S) (hcost : ∀ w ∈ records, cost w ≤ C) :
    RecordPrograms.budget cost records ≤ records.length * (6 * S + C + 7) := by
  induction records with
  | nil => simp [RecordPrograms.budget]
  | cons w ws ih =>
      have hw := hsize w (by simp)
      have hc := hcost w (by simp)
      have ht := ih (fun x hx => hsize x (by simp [hx]))
        (fun x hx => hcost x (by simp [hx]))
      simp only [RecordPrograms.budget, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem index_records_size (positions : List ℕ) (S : ℕ)
    (hpos : ∀ i ∈ positions, i ≤ S) :
    ∀ w ∈ positions.reverse.map indexWord, w.length ≤ S := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  simpa only [UniversalRowFactorLoop.indexWord_length] using
    hpos i (List.mem_reverse.mp hi)

theorem indices_length_le (positions : List ℕ) (S : ℕ)
    (hlen : positions.length ≤ S) (hpos : ∀ i ∈ positions, i ≤ S) :
    (UniversalRowTermProgram.indices positions).length ≤ indicesBound S := by
  have h := Encoding.length_encodeList_upper id (positions.reverse.map indexWord) S
    (index_records_size positions S hpos)
  simp only [List.length_map, List.length_reverse] at h
  exact h.trans (by unfold indicesBound; gcongr)

theorem factor_length_le (differences negatives : List Word) (S j : ℕ)
    (hd : ∀ x ∈ differences, x.length ≤ S) (hn : ∀ x ∈ negatives, x.length ≤ S) :
    (encodeFactor (UniversalRowFactorLoop.factor differences negatives j)).length ≤ factorBytes S := by
  have h1 := getD_length_le differences S hd j
  have h2 := getD_length_le negatives S hn j
  simp only [encodeFactor, UniversalRowFactorLoop.factor, List.length_append, Encoding.length_frame]
  unfold factorBytes
  omega

theorem factors_length_le (differences negatives : List Word) (positions : List ℕ) (S i : ℕ)
    (hlen : positions.length ≤ S)
    (hd : ∀ x ∈ differences, x.length ≤ S) (hn : ∀ x ∈ negatives, x.length ≤ S) :
    (Encoding.encodeList encodeFactor
      (UniversalRowFactorLoop.factors differences negatives i positions)).length ≤ factorsBytes S := by
  have hc : (UniversalRowFactorLoop.factors differences negatives i positions).length ≤ S := by
    simpa only [UniversalRowFactorLoop.factors, List.length_map] using
      (List.length_filter_le (fun j => decide (j ≠ i)) positions).trans hlen
  have h := Encoding.length_encodeList_upper encodeFactor
    (UniversalRowFactorLoop.factors differences negatives i positions) (factorBytes S) (by
      intro f hf
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hf
      exact factor_length_le differences negatives S j hd hn)
  exact h.trans (by unfold factorsBytes; gcongr)

theorem term_length_le (t : UniversalRowLoop.Tables) (positions : List ℕ) (S i : ℕ)
    (hlen : positions.length ≤ S)
    (hv : ∀ x ∈ t.values, x.length ≤ S) (hi : ∀ x ∈ t.inverses, x.length ≤ S)
    (hn : ∀ x ∈ t.negatives, x.length ≤ S)
    (hd : ∀ x ∈ t.differences.getD i [], x.length ≤ S) :
    (encodeTerm (UniversalRowLoop.term t positions i)).length ≤ termBytes S := by
  have h1 := getD_length_le t.values S hv i
  have h2 := getD_length_le t.inverses S hi i
  have h3 := factors_length_le (t.differences.getD i []) t.negatives positions S i hlen hd hn
  simp only [encodeTerm, UniversalRowLoop.term, UniversalRowTermProgram.term,
    List.length_append, Encoding.length_frame]
  unfold termBytes
  omega

theorem row_length_le (t : UniversalRowLoop.Tables) (positions : List ℕ) (delta limit : Word)
    (S : ℕ) (hlen : positions.length ≤ S) (hdelta : delta.length ≤ S)
    (hterm : ∀ i ∈ positions, (encodeTerm (UniversalRowLoop.term t positions i)).length ≤ termBytes S) :
    (encodeRow (UniversalRowDataProgram.row t positions delta limit)).length ≤ rowBytes S := by
  have hc : (UniversalRowDataProgram.row t positions delta limit).terms.length ≤ S := by
    simp only [UniversalRowDataProgram.row]
    split_ifs <;> simp_all
  have h := Encoding.length_encodeList_upper encodeTerm
    (UniversalRowDataProgram.row t positions delta limit).terms (termBytes S) (by
      intro term ht
      simp only [UniversalRowDataProgram.row] at ht
      split_ifs at ht with hguard
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
        exact hterm i hi
      · simp at ht)
  simp only [encodeRow, List.length_append, Encoding.length_frame]
  change 2 * delta.length + 1 + _ ≤ _
  have hh := h.trans (show 1 + (2 * termBytes S + 2) * _ ≤
      1 + (2 * termBytes S + 2) * S by gcongr)
  unfold rowBytes
  omega

theorem term_cost_le (t : UniversalRowLoop.Tables) (width rowWidth : Word)
    (positions : List ℕ) (S i : ℕ) (hlen : positions.length ≤ S)
    (hpos : ∀ j ∈ positions, j ≤ S) (hi : i ≤ S)
    (hw : width.length ≤ S) (hr : rowWidth.length ≤ S)
    (hv : ∀ x ∈ t.values, x.length ≤ S) (hinv : ∀ x ∈ t.inverses, x.length ≤ S)
    (hn : ∀ x ∈ t.negatives, x.length ≤ S)
    (hd : ∀ x ∈ t.differences.getD i [], x.length ≤ S) :
    UniversalRowTermProgram.cost t.values t.inverses t.negatives (t.differences.getD i [])
      width rowWidth positions i ≤ termBound S := by
  have hindices := indices_length_le positions S hlen hpos
  have hrecords := index_records_size positions S hpos
  have hcallback : ∀ w ∈ positions.reverse.map indexWord,
      UniversalRowFactorLoop.callbackCost width.length i w ≤ factorCallbackBound S := by
    intro w hwmem
    have hwl := hrecords w hwmem
    unfold UniversalRowFactorLoop.callbackCost factorCallbackBound
    gcongr
  have hloop := record_budget_le (UniversalRowFactorLoop.callbackCost width.length i)
    (positions.reverse.map indexWord) S (factorCallbackBound S) hrecords hcallback
  simp only [List.length_map, List.length_reverse] at hloop
  have hl : RecordPrograms.budget (UniversalRowFactorLoop.callbackCost width.length i)
      (positions.reverse.map indexWord) ≤ factorLoopBound S :=
    hloop.trans (by unfold factorLoopBound; gcongr)
  have hv' := getD_length_le t.values S hv i
  have hi' := getD_length_le t.inverses S hinv i
  have hf := factors_length_le (t.differences.getD i []) t.negatives positions S i hlen hd hn
  unfold UniversalRowTermProgram.cost UniversalRowTermFraming.termCost termBound
  gcongr

theorem source_bound_le_oai (t : UniversalRowLoop.Tables) (width rowWidth : Word)
    (positions : List ℕ) (delta limit zero one : Word) (S : ℕ)
    (valid : UniversalRowLoop.Valid t width rowWidth positions)
    (hlen : positions.length ≤ S) (hpos : ∀ i ∈ positions, i ≤ S)
    (hw : width.length ≤ S) (hr : rowWidth.length ≤ S)
    (hd : delta.length ≤ S) (hl : limit.length ≤ S)
    (hz : zero.length ≤ S) (ho : one.length ≤ S) :
    UniversalRowSourceProgram.bound t width rowWidth positions delta limit zero one ≤ sourceBound S ∧
      (rowCode zero one (zero ++ one) (UniversalRowDataProgram.row t positions delta limit)).length ≤
        sourceLengthBound S := by
  have hv : ∀ x ∈ t.values, x.length ≤ S := fun x hx => (valid.values x hx).le.trans hw
  have hinv : ∀ x ∈ t.inverses, x.length ≤ S := fun x hx => (valid.inverses x hx).le.trans hw
  have hn : ∀ x ∈ t.negatives, x.length ≤ S := fun x hx => (valid.negatives x hx).le.trans hw
  have hdiff (i : ℕ) (hi : i ∈ positions) : ∀ x ∈ t.differences.getD i [], x.length ≤ S :=
    fun x hx => (valid.differences i hi x hx).le.trans hw
  have hterms : ∀ i ∈ positions, (encodeTerm (UniversalRowLoop.term t positions i)).length ≤ termBytes S :=
    fun i hi => term_length_le t positions S i hlen hv hinv hn (hdiff i hi)
  have hrow := row_length_le t positions delta limit S hlen hd hterms
  have hinput : inputSize zero one (UniversalRowDataProgram.row t positions delta limit) ≤ inputBound S := by
    unfold inputSize inputBound
    omega
  have hrecords := index_records_size positions S hpos
  have houter := record_budget_le (UniversalRowLoop.cost t width rowWidth positions)
    (positions.reverse.map indexWord) S (termBound S) hrecords (by
      intro w hwmem
      obtain ⟨i, himem, rfl⟩ := List.mem_map.mp hwmem
      have hip := List.mem_reverse.mp himem
      simpa only [UniversalRowLoop.cost, UniversalRowFactorLoop.indexWord_length] using
        term_cost_le t width rowWidth positions S i hlen hpos (hpos i hip) hw hr hv hinv hn (hdiff i hip))
  simp only [List.length_map, List.length_reverse] at houter
  have hout : RecordPrograms.budget (UniversalRowLoop.cost t width rowWidth positions)
      (positions.reverse.map indexWord) ≤ outerLoopBound S :=
    houter.trans (by unfold outerLoopBound; gcongr)
  have hindices := indices_length_le positions S hlen hpos
  have hdata : UniversalRowDataProgram.cost t width rowWidth positions delta limit ≤ dataBound S := by
    unfold UniversalRowDataProgram.cost UniversalRowDataProgram.activeCost dataBound
    gcongr
  constructor
  · unfold UniversalRowSourceProgram.bound sourceBound
    gcongr
  · exact (rowCode_length_le zero one (zero ++ one) _).trans
      ((rowCost_quadratic zero one _).trans (by unfold sourceLengthBound; gcongr))

end SubexponentialSAT.Subexp.UniversalRowSourceBound

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound.source_bound_le_oai := @OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound.source_bound_le_oai
