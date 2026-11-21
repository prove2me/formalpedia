-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.finite_exact_gap_binary_decider
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T13:00:15.32745+00:00
-- url     : https://prove2.me/submissions/93396baf-8bb7-4949-a068-e3b47cfe6e9f

import Definitions.Def_InfoLossLAR_RuntimeBundle_03
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_reduced_basis_gap_box_exact
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_finite_cutoff_lll_poly

set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
open scoped BigOperators


section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeAffineApply
open AFT AFT.BinaryArithmetic
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open InfoLossLAR.WorstCase
open scoped BigOperators
def dot (x : List ℤ×List ℤ) : ℤ := ((x.1.zip x.2).map (fun p=>p.1*p.2)).sum
noncomputable def dotProgram : PolyProgram Automatic.enc Signed.encode dot :=
  ((PolyProgram.listZipWith Signed.encode Signed.encode 0 0 PolyProgram.intMul).comp TM2NativeEmitterCoordinates.sumProgram).congr _ (fun _=>rfl)
@[fun_prop] theorem dot_poly : Poly dot := ⟨dotProgram⟩
private theorem zip_ofFn {α β : Type} {n : ℕ} (f : Fin n→α) (g : Fin n→β) :
    (List.ofFn f).zip (List.ofFn g)=List.ofFn (fun i=>(f i,g i)) := by apply List.ext_getElem <;> simp
theorem dot_ofFn {n : ℕ} (f g : Fin n→ℤ) : dot (List.ofFn f,List.ofFn g)=∑i,f i*g i := by
  simp only [dot,zip_ofFn,List.map_ofFn,Function.comp_def,List.sum_ofFn]
end Integration9_9.TM2NativeAffineApply
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2PlatformSerialization
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime
open QAlgorithms.Complexity
open Polynomial
theorem polyTime_of_poly {f : Str → Str} (h : Poly f) : PolyTimeComputable f := by
  let P := (BooleanLists.packProgram.comp h.program).comp BooleanLists.unpackProgram
  exact ⟨(P.congr f (fun _ => rfl)).stock⟩
@[fun_prop] theorem readUnary_poly : Poly readUnary := by
  unfold readUnary
  have h : Poly (fun xs : Str => (xs, inputWidth xs + 1)) := by fun_prop
  exact Poly.pair (Poly.comp parser_take_poly h) (Poly.comp parser_drop_poly h)
theorem readUnary_rest_length (xs : Str) : (readUnary xs).2.length ≤ xs.length := by
  simp only [readUnary, List.length_drop]
  omega
@[fun_prop] theorem unarySlots_poly : Poly unarySlots := by
  unfold unarySlots
  apply Poly.list_map
  · fun_prop
  · have h : Poly (fun xs : Str => (xs, inputWidth xs)) := by fun_prop
    exact Poly.comp parser_take_poly h
@[fun_prop] theorem lengthToken_poly {α : Type} [Coding α] [Inhabited α] :
    Poly (lengthToken : List α → Str) := by
  unfold lengthToken
  fun_prop
@[fun_prop] theorem serializeWords_poly : Poly serializeWords := by
  unfold serializeWords
  have hf : Poly (List.flatten : List Str → Str) := ⟨PolyProgram.listFlatten encodeBool false⟩
  exact Poly.comp Poly.list_append (Poly.pair lengthToken_poly hf)
section RepeatedParser
variable {α : Type} [Coding α] [Inhabited α]
variable (read : Str → Str × α)
lemma parserState_encoding_length (state : ParserState α) :
    (enc state).length = 6 * state.1.length + 1 + (encodeList enc state.2).length := by
  change (encodePair (encodeList encodeBool) (encodeList enc) state).length = _
  simp only [encodePair_length, BooleanLists.length]
  omega
@[fun_prop] theorem parseStep_poly (hr : Poly read) :
    Poly (fun x : ParserState α × Unit => parseStep read x.1 x.2) := by
  unfold parseStep
  fun_prop
noncomputable def parserElementBound (hr : Poly read) : Polynomial ℕ :=
  hr.program.sizeBound.comp (3 * X)
lemma parser_element_bound (hr : Poly read) (xs : Str) :
    (enc (read xs).2).length ≤ (parserElementBound read hr).eval xs.length := by
  have h := hr.program.length_bound xs
  change (encodePair (encodeList encodeBool) enc (read xs)).length ≤
    hr.program.sizeBound.eval (encodeList encodeBool xs).length at h
  simp only [encodePair_length, BooleanLists.length] at h
  simp only [parserElementBound, eval_comp, eval_mul, eval_ofNat, eval_X]
  omega
lemma parser_fold_bounds (hr : Poly read)
    (hrest : ∀ xs, (read xs).1.length ≤ xs.length)
    (slots : List Unit) (xs : Str) (acc : List α) :
    (slots.foldl (parseStep read) (xs,acc)).1.length ≤ xs.length ∧
    (encodeList enc (slots.foldl (parseStep read) (xs,acc)).2).length ≤
      (encodeList enc acc).length + slots.length * (2 * (parserElementBound read hr).eval xs.length + 1) := by
  induction slots generalizing xs acc with
  | nil => simp only [List.foldl_nil, List.length_nil, zero_mul, add_zero, le_refl, and_self]
  | cons slot slots ih =>
    have hi := ih (read xs).1 ((read xs).2 :: acc)
    have hrx := hrest xs
    have hp := polynomial_eval_mono (parserElementBound read hr) hrx
    have he := parser_element_bound read hr xs
    constructor
    · simpa only [List.foldl_cons, parseStep] using hi.1.trans hrx
    · change (encodeList enc
        (slots.foldl (parseStep read) ((read xs).1, (read xs).2 :: acc)).2).length ≤ _
      have hm : slots.length * (2 * (parserElementBound read hr).eval (read xs).1.length + 1) ≤
          slots.length * (2 * (parserElementBound read hr).eval xs.length + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      simp only [EncodedList.cons_length] at hi
      simp only [List.length_cons]
      nlinarith
noncomputable def parserFoldBound (hr : Poly read) : Polynomial ℕ :=
  X + X * (2 * parserElementBound read hr + 1)
lemma parser_fold_state_bound (hr : Poly read)
    (hrest : ∀ xs, (read xs).1.length ≤ xs.length)
    (as : List Unit) (b : ParserState α) (pre suf : List Unit) (he : as = pre ++ suf) :
    (enc (pre.foldl (parseStep read) b)).length ≤
      (parserFoldBound read hr).eval (encodePair (encodeList (enc : Unit → Str)) enc (as,b)).length := by
  let N := (encodePair (encodeList (enc : Unit → Str)) enc (as,b)).length
  have hN : N = 2 * (encodeList (enc : Unit → Str) as).length + 1 +
      (6 * b.1.length + 1 + (encodeList enc b.2).length) := by
    simp only [N, encodePair_length, parserState_encoding_length]
  have hslots : pre.length ≤ N := by
    have h := EncodedList.length_le (enc : Unit → Str) as
    have hl : pre.length ≤ as.length := by simp only [he, List.length_append]; omega
    omega
  have hx : b.1.length ≤ N := by omega
  have hh := parser_fold_bounds read hr hrest pre b.1 b.2
  simp only [Prod.eta] at hh
  have hp := polynomial_eval_mono (parserElementBound read hr) hx
  have hm : pre.length * (2 * (parserElementBound read hr).eval b.1.length + 1) ≤
      N * (2 * (parserElementBound read hr).eval N + 1) := Nat.mul_le_mul hslots (by omega)
  change (enc (pre.foldl (parseStep read) b)).length ≤ (parserFoldBound read hr).eval N
  rw [parserState_encoding_length]
  simp only [parserFoldBound, eval_add, eval_mul, eval_X, eval_ofNat, eval_one]
  omega
@[fun_prop] theorem parserFold_poly (hr : Poly read)
    (hrest : ∀ xs, (read xs).1.length ≤ xs.length) :
    Poly (fun x : List Unit × ParserState α => x.1.foldl (parseStep read) x.2) :=
  ⟨(parseStep_poly read hr).program.listFold () (parserFoldBound read hr)
    (parser_fold_state_bound read hr hrest)⟩
@[fun_prop] theorem readList_poly (hr : Poly read)
    (hrest : ∀ xs, (read xs).1.length ≤ xs.length) : Poly (readList read) := by
  unfold readList
  have hs : Poly (fun xs : Str =>
      (unarySlots xs).foldl (parseStep read) ((readUnary xs).2, ([] : List α))) :=
    by
      have h : Poly (fun xs : Str => (unarySlots xs, ((readUnary xs).2, ([] : List α)))) :=
        Poly.pair unarySlots_poly (Poly.pair (Poly.comp Poly.snd readUnary_poly) (OAI.MetricKMedian.Binary.Automatic.Poly.const (α := Str) ([] : List α)))
      exact Poly.comp (parserFold_poly read hr hrest) h
  exact Poly.pair (Poly.comp Poly.fst hs)
    (Poly.comp parser_reverse_poly (Poly.comp Poly.snd hs))
end RepeatedParser
end Integration9_9.TM2PlatformSerialization
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.LARPlatformEncoding
open InfoLossLAR.WorstCase QAlgorithms.Complexity
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime
open TM2PlatformSerialization
@[fun_prop] theorem markedStep_poly : Poly (fun x : MarkedState × Bool => markedStep x.1 x.2) := by
  unfold markedStep
  fun_prop
private theorem markedState_length (state : MarkedState) :
    (enc state).length=10+6*state.2.1.length+3*state.2.2.length := by
  change (encodePair (encodePair encodeBool encodeBool)
    (encodePair (encodeList encodeBool) (encodeList encodeBool)) state).length = _
  simp only [encodePair_length,encodeBool,List.length_singleton,BooleanLists.length]
  omega
private theorem markedStep_bound (state : MarkedState) (bit : Bool) :
    (enc (markedStep state bit)).length ≤ (enc state).length+2*(2*(enc bit).length+1) := by
  have hb : (enc bit).length=1 := rfl
  rw [hb,markedState_length]
  unfold markedStep
  split_ifs <;> rw [markedState_length] <;> simp <;> omega
@[fun_prop] theorem readMarked_poly : Poly readMarked := by
  have hfold : Poly (fun x : Str × MarkedState => x.1.foldl markedStep x.2) :=
    ⟨markedStep_poly.program.listFoldLinear false 2 markedStep_bound⟩
  have hstate : Poly (fun xs : Str => xs.foldl markedStep ((false,false),([],[]))) :=
    Poly.comp (f := fun x : Str × MarkedState => x.1.foldl markedStep x.2)
      (g := fun xs : Str => (xs,((false,false),([],[])))) hfold (by fun_prop)
  unfold readMarked
  exact Poly.pair (Poly.comp parser_reverse_poly (Poly.comp Poly.snd (Poly.comp Poly.snd hstate)))
    (Poly.comp parser_reverse_poly (Poly.comp Poly.fst (Poly.comp Poly.snd hstate)))
@[fun_prop] theorem readB_poly : Poly readB := by
  unfold readB
  exact Poly.pair (Poly.comp Poly.fst readMarked_poly)
    (Poly.comp bitValue_poly (Poly.comp Poly.snd readMarked_poly))
private theorem markedStep_rest_bound (state : MarkedState) (bit : Bool) :
    (markedStep state bit).2.2.length ≤ state.2.2.length+1 := by
  unfold markedStep
  split_ifs <;> simp <;> omega
private theorem marked_fold_rest_bound (xs : Str) (state : MarkedState) :
    (xs.foldl markedStep state).2.2.length ≤ state.2.2.length+xs.length := by
  induction xs generalizing state with
  | nil => simp
  | cons bit xs ih =>
    have h := ih (markedStep state bit)
    have hs := markedStep_rest_bound state bit
    simp only [List.foldl_cons,List.length_cons]
    omega
theorem readB_rest_length (xs : Str) : (readB xs).1.length ≤ xs.length := by
  have h := marked_fold_rest_bound xs ((false,false),([],[]))
  simpa only [readB,readMarked,List.length_reverse,List.length_nil,zero_add] using h
@[fun_prop] theorem readS_poly : Poly readS := by
  unfold readS
  exact Poly.pair (Poly.comp parser_drop_poly readB_poly) (Poly.comp parser_take_poly readB_poly)
@[fun_prop] theorem binarySlots_poly : Poly binarySlots := by
  unfold binarySlots
  have ht : Poly (fun xs : Str => xs.take (readB xs).2) :=
    Poly.comp parser_take_poly (Poly.pair Poly.identity (Poly.comp Poly.snd readB_poly))
  exact Poly.list_map (by fun_prop) ht
section BinaryList
variable {α : Type} [Coding α] [Inhabited α]
variable (read : Str → Str × α)
@[fun_prop] theorem readBinaryList_poly (hr : Poly read)
    (hrest : ∀ xs,(read xs).1.length ≤ xs.length) : Poly (readBinaryList read) := by
  have hs : Poly (fun xs : Str =>
      (binarySlots xs).foldl (parseStep read) ((readB xs).1,([] : List α))) :=
    Poly.comp (parserFold_poly read hr hrest)
      (Poly.pair binarySlots_poly
        (Poly.pair (Poly.comp Poly.fst readB_poly) (OAI.MetricKMedian.Binary.Automatic.Poly.const (α := Str) ([] : List α))))
  unfold readBinaryList
  exact Poly.pair (Poly.comp Poly.fst hs)
    (Poly.comp parser_reverse_poly (Poly.comp Poly.snd hs))
theorem readBinaryList_rest_length (hr : Poly read)
    (hrest : ∀ xs,(read xs).1.length ≤ xs.length) (xs : Str) :
    (readBinaryList read xs).1.length ≤ xs.length :=
  (parser_fold_bounds read hr hrest (binarySlots xs) (readB xs).1 []).1.trans (readB_rest_length xs)
end BinaryList
end Integration9_9.LARPlatformEncoding
end
section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.TM2NativeAffineEncoding
open AFT AFT.BinaryArithmetic QAlgorithms.Complexity
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open InfoLossLAR.WorstCase LARPlatformEncoding
def readInteger (xs : Str) : Str×ℤ :=
  let magnitude:=readB xs.tail
  (magnitude.1,Signed.value (xs[0]?.getD false) magnitude.2)
@[fun_prop] theorem readInteger_poly : Poly readInteger := by
  have hs : Poly (fun x : Bool×ℕ=>Signed.value x.1 x.2) := ⟨PolyProgram.intFromParts⟩
  unfold readInteger
  fun_prop
theorem readInteger_rest_length (xs : Str) : (readInteger xs).1.length ≤ xs.length :=
  (readB_rest_length xs.tail).trans (by simp)
@[simp] theorem readInteger_append (z : ℤ) (suffix : Str) : readInteger (encI z++suffix)=(suffix,z) := by
  simp only [readInteger,encI,List.cons_append,List.tail_cons,readB_append,List.getElem?_cons_zero,Option.getD_some]
  exact congrArg (fun x : ℤ=>(suffix,x)) (Signed.value_parts z)
def readVector : Str → Str×List ℤ := readBinaryList readInteger
@[fun_prop] theorem readVector_poly : Poly readVector := readBinaryList_poly readInteger readInteger_poly readInteger_rest_length
theorem readVector_rest_length (xs : Str) : (readVector xs).1.length ≤ xs.length :=
  readBinaryList_rest_length readInteger readInteger_poly readInteger_rest_length xs
@[simp] theorem readVector_append {n : ℕ} (v : Fin n→ℤ) (suffix : Str) :
    readVector (encVec encI v++suffix)=(suffix,List.ofFn v) := by
  unfold readVector encVec
  have h:=readBinaryList_append_mapped readInteger encI id (fun z=>by simp [encI]) readInteger_append (List.ofFn v) suffix
  simpa only [List.map_id] using h
def readMatrix : Str → Str×List (List ℤ) := readBinaryList readVector
@[fun_prop] theorem readMatrix_poly : Poly readMatrix := readBinaryList_poly readVector readVector_poly readVector_rest_length
@[simp] theorem readMatrix_append {d n : ℕ} (Q : Matrix (Fin d) (Fin n) ℤ) (suffix : Str) :
    readMatrix (encMat encI Q++suffix)=(suffix,List.ofFn (fun i=>List.ofFn (Q i))) := by
  unfold readMatrix encMat
  have h:=readBinaryList_append_mapped readVector (encVec encI : (Fin n→ℤ)→Str)
    (fun v=>List.ofFn v) (fun v=>encL_length_pos encI (List.ofFn v)) readVector_append (List.ofFn Q) suffix
  simpa only [List.map_ofFn,Function.comp_def] using h
end Integration9_9.TM2NativeAffineEncoding
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Integration9_9.LARCoinLayout
open InfoLossLAR.WorstCase QAlgorithms.Complexity Function Polynomial
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime LARPlatformEncoding TM2PlatformSerialization
noncomputable def rawPolyProgram {f : Str → Str}
    (h : OAI.MetricKMedian.Binary.Automatic.Poly f) : PolyProgram id id f :=
  ((BooleanLists.packProgram.comp h.program).comp BooleanLists.unpackProgram).congr f (fun _ => rfl)
end Integration9_9.LARCoinLayout
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open QAlgorithms.Complexity
open Integration9_9
open Integration9_9.TM2NativeAffineEncoding (readInteger readInteger_append)
open Integration9_9.LARPlatformEncoding
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
namespace InfoLossLAR.WorstCase.RegevSketch
abbrev GapInput := List (List ℤ) × ℚ
def gapRat (word : Str) : ℚ :=
  let num := readInteger word
  mkRat num.2 (readB num.1).2
@[fun_prop] theorem gapRat_poly : Poly gapRat := by
  unfold gapRat
  fun_prop
theorem gapRat_encoded (r : ℚ) : gapRat (encQ r) = r := by
  simp only [gapRat, encQ, readInteger_append]
  have h := readB_append r.den ([] : Str)
  rw [List.append_nil] at h
  rw [h]
  exact Rat.mkRat_self r
def readGap (word : Str) : GapInput :=
  let first := readS word
  let second := readS first.1
  ((TM2NativeAffineEncoding.readMatrix first.2).2, gapRat second.2)
@[fun_prop] theorem readGap_poly : Poly readGap := by
  unfold readGap
  fun_prop
theorem readGap_encoded {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) :
    readGap (encGapInstance B δ) = (List.ofFn (fun i => List.ofFn (B i)), δ) := by
  have hend (word : Str) : readS (encS word) = ([], word) := by
    simpa only [List.append_nil] using readS_append word []
  have hmat : TM2NativeAffineEncoding.readMatrix (encMat encI B) =
      ([], List.ofFn (fun i => List.ofFn (B i))) := by
    simpa only [List.append_nil] using TM2NativeAffineEncoding.readMatrix_append B []
  simp only [readGap, encGapInstance, encPair, readS_append, hend, hmat, gapRat_encoded]
def rawGap (f : GapInput → Bool) (word : Str) : Str := [f (readGap word)]
theorem rawGap_poly {f : GapInput → Bool} (hf : Poly f) : Poly (rawGap f) := by
  unfold rawGap
  fun_prop
theorem finite_exact_gap_binary_decider_of_typed (cutoff : ℕ) (f : GapInput → Bool) (hf : Poly f)
    (hcorrect : ∀ n : ℕ, 1 ≤ n → n < cutoff →
      ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 → ∀ δ : ℚ, 0 < δ →
        (f (List.ofFn (fun i => List.ofFn (B i)), δ) = true ↔ lam1 B ≤ δ)) :
    ∃ f : Str → Str, Nonempty (OAI.MetricKMedian.Binary.PolyProgram id id f) ∧
      ∀ n : ℕ, 1 ≤ n → n < cutoff →
        ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
          ∀ δ : ℚ, 0 < δ →
            ((f (encGapInstance B δ))[0]? = some true ↔ lam1 B ≤ (δ : ℝ)) := by
  refine ⟨rawGap f, ⟨LARCoinLayout.rawPolyProgram (rawGap_poly hf)⟩, ?_⟩
  intro n hn hc B hB δ hδ
  simp only [rawGap, readGap_encoded, List.getElem?_cons_zero, Option.some.injEq]
  exact hcorrect n hn hc B hB δ hδ
end InfoLossLAR.WorstCase.RegevSketch
end
section
set_option backward.isDefEq.respectTransparency false
namespace InfoLossLAR.WorstCase.NativeLLL

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Integration9_9.TM2NativeAffineApply (dot dot_ofFn)
def gapBox (n : ℕ) : ℕ := n * 2^(n-1) * (n+1)^n

def gapAlphabet (cap : ℕ) : List ℤ :=
  (List.range (2 * cap + 1)).map (fun k : ℕ => (k : ℤ) - (cap : ℤ))
def gapWords (alphabet : List ℤ) : ℕ → List (List ℤ)
  | 0 => [[]]
  | n+1 => alphabet.flatMap (fun c => (gapWords alphabet n).map (List.cons c))
def gapPool (cutoff : ℕ) : List (List ℤ) :=
  (List.range cutoff).flatMap (fun n => gapWords (gapAlphabet (gapBox n)) n)
theorem gapAlphabet_contains {cap : ℕ} {x : ℤ} (h : x.natAbs ≤ cap) :
    x ∈ gapAlphabet cap := by
  have hc : |x| ≤ (cap : ℤ) := by
    rw [←Int.natCast_natAbs]
    exact_mod_cast h
  obtain ⟨hl,hu⟩ := abs_le.mp hc
  let k := (x + (cap : ℤ)).toNat
  have hk : (k : ℤ) = x + (cap : ℤ) := Int.toNat_of_nonneg (by omega)
  apply List.mem_map.mpr
  refine ⟨k, List.mem_range.mpr ?_, by omega⟩
  omega
theorem gapWords_contains {alphabet : List ℤ} (xs : List ℤ)
    (h : ∀ x ∈ xs, x ∈ alphabet) :
    xs ∈ gapWords alphabet xs.length := by
  induction xs with
  | nil => simp [gapWords]
  | cons x xs ih =>
    apply List.mem_flatMap.mpr
    refine ⟨x, h x (by simp), List.mem_map.mpr ⟨xs, ?_, rfl⟩⟩
    exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
theorem gapPool_contains {cutoff n : ℕ} (hn : n < cutoff)
    (z : Fin n → ℤ) (h : ∀ i, (z i).natAbs ≤ gapBox n) :
    List.ofFn z ∈ gapPool cutoff := by
  apply List.mem_flatMap.mpr
  refine ⟨n, List.mem_range.mpr hn, ?_⟩
  have hall : ∀ x ∈ List.ofFn z, x ∈ gapAlphabet (gapBox n) := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact gapAlphabet_contains (h i)
  simpa only [List.length_ofFn] using gapWords_contains (List.ofFn z) hall
abbrev GapRows := List (List ℤ)
def gapRowsMul (input : GapRows × List ℤ) : List ℤ :=
  input.1.map (fun row => dot (row,input.2))
@[fun_prop] theorem gapRowsMul_poly : Poly gapRowsMul := by
  unfold gapRowsMul
  fun_prop
def gapSqLength (xs : List ℤ) : ℚ := dot (xs,xs)
@[fun_prop] theorem gapSqLength_poly : Poly gapSqLength := by
  unfold gapSqLength
  fun_prop
def gapCandidate (input : (GapRows × ℚ) × List ℤ) : Bool :=
  let cost := gapSqLength (gapRowsMul (input.1.1,input.2))
  decide (input.2.length = input.1.1.length) &&
    decide (0 < cost) && decide (cost ≤ input.1.2 * input.1.2)
@[fun_prop] theorem gapCandidate_poly : Poly gapCandidate := by
  unfold gapCandidate
  fun_prop
def gapReducedSearch (cutoff : ℕ) (data : GapRows × ℚ) : Bool :=
  decide (0 < ((gapPool cutoff).filter (fun z => gapCandidate (data,z))).length)
@[fun_prop] theorem gapReducedSearch_poly (cutoff : ℕ) : Poly (gapReducedSearch cutoff) := by
  unfold gapReducedSearch
  have h : Poly (fun input : GapRows × ℚ => (gapPool cutoff).filter
      (fun z => gapCandidate (input,z))) :=
    Poly.list_filter (f := fun input z => gapCandidate (input,z)) gapCandidate_poly (Automatic.Poly.const _)
  exact Poly.nat_lt_comp (Automatic.Poly.const _) (Poly.comp Poly.list_length h)
def gapBasisRows {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : GapRows :=
  List.ofFn (fun i => List.ofFn (B i))
theorem gapRowsMul_value {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) :
    gapRowsMul (gapBasisRows B,List.ofFn z) = List.ofFn (B.mulVec z) := by
  rw [gapRowsMul, gapBasisRows, List.map_ofFn]
  exact congrArg List.ofFn (funext (fun i => dot_ofFn (B i) z))
theorem gapAlphabet_sound {cap : ℕ} {x : ℤ} (h : x ∈ gapAlphabet cap) :
    x.natAbs ≤ cap := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
  have hr := List.mem_range.mp hk
  have hri : (k : ℤ) < 2 * (cap : ℤ) + 1 := by exact_mod_cast hr
  have ha : |(k : ℤ) - (cap : ℤ)| ≤ (cap : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
  exact_mod_cast (show (↑(((k : ℤ) - (cap : ℤ)).natAbs) : ℤ) ≤ (cap : ℤ) by
    rwa [Int.natCast_natAbs])

theorem gapWords_sound {alphabet : List ℤ} {n : ℕ} {word : List ℤ}
    (h : word ∈ gapWords alphabet n) : word.length = n ∧ ∀ x ∈ word, x ∈ alphabet := by
  induction n generalizing word with
  | zero => simp [gapWords] at h; subst word; simp
  | succ n ih =>
    obtain ⟨a, ha, hw⟩ := List.mem_flatMap.mp h
    obtain ⟨rest, hrest, rfl⟩ := List.mem_map.mp hw
    obtain ⟨hlen, hmem⟩ := ih hrest
    exact ⟨by simp [hlen], fun x hx => (List.mem_cons.mp hx).elim (fun he => he ▸ ha) (hmem x)⟩

theorem gapPool_sound {cutoff n : ℕ} (z : Fin n → ℤ) (h : List.ofFn z ∈ gapPool cutoff) :
    ∀ i, (z i).natAbs ≤ gapBox n := by
  obtain ⟨m, _, hm⟩ := List.mem_flatMap.mp h
  obtain ⟨hl, hw⟩ := gapWords_sound hm
  have he : n = m := by simpa only [List.length_ofFn] using hl
  rw [←he] at hw
  exact fun i => gapAlphabet_sound (hw (z i) (List.mem_ofFn.mpr ⟨i, rfl⟩))

theorem gapCandidate_search_value {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ)
    (z : Fin n → ℤ) :
    let normSq : ℚ := ((∑ i : Fin n, ((B.mulVec z) i)^2 : ℤ) : ℚ)
    gapCandidate ((gapBasisRows B, δ), List.ofFn z) = true ↔
      0 < normSq ∧ normSq ≤ δ^2 := by
  intro normSq
  simp only [gapCandidate]
  rw [gapRowsMul_value]
  simp only [gapSqLength, dot_ofFn, gapBasisRows,
    List.length_ofFn, decide_true, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq,
    normSq, pow_two]

theorem gapReducedSearch_from_box (cutoff : ℕ) {n : ℕ} (hn : 0 < n)
    (hcutoff : n < cutoff) (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (δ : ℚ) (hδ : 0 ≤ δ) :
    gapReducedSearch cutoff (gapBasisRows (basis B), δ) = true ↔ lam1 B ≤ (δ : ℝ) := by
  have hbox := RegevSketch.reduced_basis_gap_box_exact hn B hB δ hδ
  dsimp only at hbox
  rw [hbox]
  simp only [gapReducedSearch, decide_eq_true_eq, List.length_pos_iff_exists_mem, List.mem_filter]
  constructor
  · rintro ⟨word, hw, haccept⟩
    have hlen : word.length = n := by
      have hshape := haccept
      simp only [gapCandidate, Bool.and_eq_true, decide_eq_true_eq] at hshape
      simpa [gapBasisRows] using hshape.1.1
    let z : Fin n → ℤ := fun i => word[i.val]'(by rw [hlen]; exact i.isLt)
    have hword : List.ofFn z = word := by
      apply List.ext_getElem
      · simpa using hlen.symm
      · intro i hi hj
        simp [z]
    rw [←hword] at hw haccept
    exact ⟨z, gapPool_sound z hw, (gapCandidate_search_value (basis B) δ z).mp haccept⟩
  · rintro ⟨z, hz, hv⟩
    exact ⟨List.ofFn z, gapPool_contains hcutoff z hz,
      (gapCandidate_search_value (basis B) δ z).mpr hv⟩

end InfoLossLAR.WorstCase.NativeLLL
end

open QAlgorithms.Complexity InfoLossLAR.WorstCase
open InfoLossLAR.WorstCase.RegevSketch InfoLossLAR.WorstCase.NativeLLL
open OAI.MetricKMedian.Binary.Automatic

theorem solution (cutoff : ℕ) :
    ∃ f : Str → Str, Nonempty (OAI.MetricKMedian.Binary.PolyProgram id id f) ∧
      ∀ n : ℕ, 1 ≤ n → n < cutoff →
        ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
          ∀ δ : ℚ, 0 < δ →
            ((f (encGapInstance B δ))[0]? = some true ↔ lam1 B ≤ (δ : ℝ)) := by
  obtain ⟨reduce, hpoly, hreduce⟩ := finite_cutoff_lll_poly cutoff
  let decideGap : GapInput → Bool := fun input =>
    gapReducedSearch cutoff (reduce input.1, input.2)
  have hp : Poly decideGap :=
    Poly.comp (gapReducedSearch_poly cutoff) (Poly.pair (Poly.comp hpoly Poly.fst) Poly.snd)
  refine finite_exact_gap_binary_decider_of_typed cutoff decideGap hp ?_
  intro n hn hc B hB δ hδ
  change gapReducedSearch cutoff (reduce (gapBasisRows B), δ) = true ↔ lam1 B ≤ (δ : ℝ)
  rw [show reduce (gapBasisRows B) = gapBasisRows (basis B) from hreduce n hn hc B hB]
  exact gapReducedSearch_from_box cutoff hn hc B hB δ hδ.le
