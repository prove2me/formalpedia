-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSearch.independent_coefficient_batch_mqpt
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T14:07:03.543725+00:00
-- url     : https://prove2.me/submissions/993630be-d03b-4625-8f74-2239bb556c12
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_uniform_raw_repetitions
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_02
import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Integration9_9.LARPlatformEncoding (readS readS_append readB readB_append
  serializeBinaryWords serializeBinaryWords_map encL_length_pos readBinaryList_append_mapped)
open Integration9_9.TM2NativeAffineEncoding (readVector readVector_append readMatrix
  readMatrix_append)
open Integration9_9.TM2NativeAffineEmitter (serializeVector serializeMatrix)
open scoped BigOperators Classical

namespace CoefficientBatch

def splitFrame (w : Str) : Str × Str :=
  ((readS w).2, (readS (readS w).1).2)

@[fun_prop] theorem splitFrame_poly : Poly splitFrame := by unfold splitFrame; fun_prop

@[simp] theorem splitFrame_pair (a b : Str) : splitFrame (encPair a b) = (a,b) := by
  simp only [splitFrame, encPair, readS_append]
  have h := readS_append b []
  simpa using congrArg (fun z : Str × Str => (a,z.2)) h

def countWord (w : Str) : Str := (splitFrame (splitFrame (splitFrame w).2).2).1

@[fun_prop] theorem countWord_poly : Poly countWord := by unfold countWord; fun_prop

def requestWord (w : Str) : Str :=
  let outer := splitFrame w
  let second := splitFrame outer.2
  let numbers := splitFrame second.2
  let precision := numbers.1.flatMap (fun _ => true :: numbers.2)
  encPair outer.1 (encPair second.1 (encPair (unary 1) precision))

@[fun_prop] theorem requestWord_poly : Poly requestWord := by unfold requestWord; fun_prop

theorem countWord_dgs {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (m b : ℕ) :
    (countWord (dgsInput B r m b)).length = m := by
  simp [countWord, dgsInput, unary]

theorem requestWord_dgs {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (m b : ℕ) :
    requestWord (dgsInput B r m b) = dgsInput B r 1 (m * (b+1)) := by
  have h : (unary m).flatMap (fun _ => true :: unary b) = unary (m * (b+1)) := by
    induction m with
    | zero => simp [unary]
    | succ m ih =>
      change (true :: unary b) ++ (unary m).flatMap (fun _ => true :: unary b) =
        unary ((m+1)*(b+1))
      rw [ih,Nat.succ_mul,Nat.add_comm (m*(b+1)) (b+1)]
      exact (List.replicate_add (b+1) (m*(b+1)) true).symm
  simp only [requestWord,dgsInput,splitFrame_pair,h]

def row (w : Str) : List ℤ := (readVector w).2
@[fun_prop] theorem row_poly : Poly row := by unfold row; fun_prop

def every (xs : List Bool) : Bool := xs.all id
@[fun_prop] theorem every_poly : Poly every := ⟨PolyProgram.listAll (PolyProgram.identity encodeBool) false⟩

def bitEq (x : Bool × Bool) : Bool := if x.1 then x.2 else !x.2
@[fun_prop] theorem bitEq_poly : Poly bitEq := by unfold bitEq; fun_prop
private theorem bitEq_true (x y : Bool) : bitEq (x,y) = true ↔ x = y := by
  cases x <;> cases y <;> decide

/-- Check each position of the proposed prefix, including the length test. -/
def prefixTest (x : Str × Str) : Bool :=
  decide (x.1.length ≤ x.2.length) && every ((List.range x.1.length).map
    (fun j => bitEq (x.1[j]?.getD false, x.2[j]?.getD false)))

@[fun_prop] theorem prefixTest_poly : Poly prefixTest := by
  have hi : Poly (fun x : Str × Str => List.range x.1.length) :=
    Poly.comp (f := fun xs : Str => List.range xs.length) (g := fun x : Str × Str => x.1)
      (Poly.list_indices (α := Bool)) Poly.fst
  have hl : Poly (fun x : (Str × Str) × ℕ => x.1.1[x.2]?.getD false) := by fun_prop
  have hr : Poly (fun x : (Str × Str) × ℕ => x.1.2[x.2]?.getD false) := by fun_prop
  have ht := Poly.comp bitEq_poly (Poly.pair hl hr)
  have hm : Poly (fun x : Str × Str => (List.range x.1.length).map
      (fun j => bitEq (x.1[j]?.getD false, x.2[j]?.getD false))) :=
    Poly.list_map ht hi
  unfold prefixTest
  fun_prop

theorem prefixTest_exact (a b : Str) : prefixTest (a,b) = true ↔ a <+: b := by
  simp only [prefixTest, Bool.and_eq_true, decide_eq_true_eq, every, List.all_eq_true,
    List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    id_eq, bitEq_true]
  constructor
  · rintro ⟨hlen,hbits⟩
    apply List.prefix_iff_eq_take.mpr
    apply List.ext_getElem (by simp [hlen])
    intro j hj hj'
    have hb : j < b.length := lt_of_lt_of_le hj hlen
    have he := hbits j hj
    simpa [List.getElem?_eq_getElem hj,List.getElem?_eq_getElem hb] using he
  · rintro ⟨tail,rfl⟩
    refine ⟨by simp,?_⟩
    intro j hj
    simp [List.getElem?_append_left hj]

def validRow (w : Str) : Bool := prefixTest (serializeVector (row w), w)
@[fun_prop] theorem validRow_poly : Poly validRow := by unfold validRow; fun_prop

/-- A failed framing check writes a different outer length. No appended padding
can turn this header into a successful pool of the requested length. -/
def pack (words : List Str) : Str :=
  if every (words.map validRow) then serializeMatrix (words.map row)
  else encB (words.length + 1)

@[fun_prop] theorem pack_poly : Poly pack := by unfold pack; fun_prop

private theorem vector_code (v : List ℤ) : serializeVector v = encL encI v :=
  serializeBinaryWords_map encI v

private theorem matrix_code (v : List (List ℤ)) :
    serializeMatrix v = encL serializeVector v := serializeBinaryWords_map serializeVector v

private theorem vector_ofFn {n : ℕ} (z : Fin n → ℤ) :
    serializeVector (List.ofFn z) = encVec encI z := vector_code _

private theorem matrix_ofFn {n m : ℕ} (z : Fin m → Fin n → ℤ) :
    serializeMatrix (List.ofFn (fun i => List.ofFn (z i))) = encVec (encVec encI) z := by
  unfold serializeMatrix
  simp only [List.map_ofFn, Function.comp_def,vector_ofFn]
  simpa only [List.map_ofFn,Function.comp_def,encVec] using
    serializeBinaryWords_map (encVec encI) (List.ofFn z)

private theorem read_rows (rows : List (List ℤ)) (suffix : Str) :
    readMatrix (serializeMatrix rows ++ suffix) = (suffix,rows) := by
  have hread (v : List ℤ) (rest : Str) : readVector (serializeVector v ++ rest) = (rest,v) := by
    have h := readVector_append v.get rest
    rw [← vector_ofFn, List.ofFn_get] at h
    exact h
  rw [matrix_code]
  simpa only [readMatrix,List.map_id] using readBinaryList_append_mapped
    readVector serializeVector id (fun v => vector_code v ▸ encL_length_pos encI v)
      hread rows suffix

theorem row_unique {n : ℕ} {u v : Fin n → ℤ} {w : Str}
    (hu : encVec encI u <+: w) (hv : encVec encI v <+: w) : u = v := by
  obtain ⟨s,hs⟩ := hu
  obtain ⟨t,ht⟩ := hv
  have h := congrArg (fun a : Str => (readVector a).2) (hs.trans ht.symm)
  simpa only [readVector_append, List.ofFn_inj] using h

private theorem valid_of_prefix {n : ℕ} {v : Fin n → ℤ} {w : Str} (h : encVec encI v <+: w) :
    validRow w = true ∧ row w = List.ofFn v := by
  obtain ⟨s,rfl⟩ := h
  simp only [row,validRow,readVector_append,vector_ofFn,prefixTest_exact]
  exact ⟨⟨s,rfl⟩,True.intro⟩

private theorem all_valid {m : ℕ} (w : Fin m → Str) :
    every ((List.ofFn w).map validRow) = true ↔ ∀ i, validRow (w i) = true := by
  simp [every, List.all_eq_true, List.mem_ofFn]

theorem pack_prefix {n m : ℕ} (w : Fin m → Str) (z : Fin m → Fin n → ℤ) (tail : Str) :
    encVec (encVec encI) z <+: pack (List.ofFn w) ++ tail ↔ ∀ i, encVec encI (z i) <+: w i := by
  constructor
  · intro hp
    by_cases hvalid : every ((List.ofFn w).map validRow) = true
    · rw [pack,if_pos hvalid] at hp
      obtain ⟨s,hs⟩ := hp
      have he := congrArg (fun a : Str => (readMatrix a).2) hs
      change (readMatrix (encMat encI z ++ s)).2 = (readMatrix (_ ++ tail)).2 at he
      simp only [readMatrix_append,read_rows,List.map_ofFn,Function.comp_def,List.ofFn_inj] at he
      intro i
      have hi := (all_valid w).mp hvalid i
      apply (prefixTest_exact _ _).mp at hi
      rw [← congrFun he i,vector_ofFn] at hi
      exact hi
    · rw [pack,if_neg hvalid,List.length_ofFn] at hp
      obtain ⟨s,hs⟩ := hp
      have he := congrArg (fun a : Str => (readB a).2) hs
      simp only [encVec,encL,List.length_ofFn,List.append_assoc,readB_append] at he
      omega
  · intro hs
    have hv := (all_valid w).mpr fun i => (valid_of_prefix (hs i)).1
    have hr : (List.ofFn w).map row = List.ofFn (fun i => List.ofFn (z i)) := by
      simp only [List.map_ofFn,Function.comp_def,List.ofFn_inj]
      exact funext fun i => (valid_of_prefix (hs i)).2
    rw [pack,if_pos hv,hr,matrix_ofFn]
    exact ⟨tail,rfl⟩

end CoefficientBatch

set_option autoImplicit false
open scoped BigOperators Classical
namespace CoefficientBatch

/-- Group finite measurement records by a partial decoding with unique answers.
The answer space need not be finite, and a record may fail to decode. -/
theorem group_records {Y Z : Type} [Fintype Y] (m : ℕ) (mass : Y → ℝ)
    (R : Y → Z → Prop) (unique : ∀ y a b, R y a → R y b → a = b)
    (E : (Fin m → Z) → Prop) :
    (∑ ys : Fin m → Y, (∏ i, mass (ys i)) *
      (if ∃ zs, (∀ i, R (ys i) (zs i)) ∧ E zs then 1 else 0)) =
    ∑' zs : Fin m → Z, (∏ i, (∑ y, if R y (zs i) then mass y else 0)) *
      (if E zs then 1 else 0) := by
  classical
  let matchEvent (ys : Fin m → Y) (zs : Fin m → Z) := (∀ i, R (ys i) (zs i)) ∧ E zs
  let cell (ys : Fin m → Y) (zs : Fin m → Z) : ℝ :=
    if matchEvent ys zs then ∏ i, mass (ys i) else 0
  have hrow (ys : Fin m → Y) : HasSum (cell ys)
      ((∏ i, mass (ys i)) * (if ∃ zs, matchEvent ys zs then 1 else 0)) := by
    by_cases h : ∃ zs, matchEvent ys zs
    · obtain ⟨a,ha⟩ := h
      have hsingle : HasSum (cell ys) (cell ys a) := hasSum_single a (by
        intro b hba
        apply if_neg
        intro hb
        apply hba
        exact funext fun i => unique (ys i) (b i) (a i) (hb.1 i) (ha.1 i))
      simpa only [cell,if_pos ha,if_pos (show ∃ zs, matchEvent ys zs from ⟨a,ha⟩),mul_one]
        using hsingle
    · have hn : ∀ z, ¬ matchEvent ys z := fun z hz => h ⟨z,hz⟩
      simp [cell,hn]
  have hcolumn (zs : Fin m → Z) :
      (∑ ys, cell ys zs) = (∏ i, (∑ y, if R y (zs i) then mass y else 0)) *
        (if E zs then 1 else 0) := by
    by_cases he : E zs
    · rw [if_pos he,mul_one,Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro ys _
      by_cases hr : ∀ i, R (ys i) (zs i)
      · simp [cell,matchEvent,hr,he]
      · obtain ⟨j,hj⟩ := not_forall.mp hr
        simp only [cell,if_neg (show ¬ matchEvent ys zs from fun h => hr h.1)]
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        exact if_neg hj
    · simp [cell,matchEvent,he]
  have grouped := hasSum_sum (s := (Finset.univ : Finset (Fin m → Y))) (fun ys _ => hrow ys)
  exact (grouped.congr_fun (fun zs => (hcolumn zs).symm)).tsum_eq.symm

end CoefficientBatch

open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open InfoLossLAR.WorstCase.RegevSearch CoefficientBatch
open scoped BigOperators Classical

theorem solution (H : MFamily) (hH : IsMQPT H) :
    ∃ G : MFamily, IsMQPT G ∧
      ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (count budget : ℕ),
        let precision := count * (budget + 1)
        let draw (z : Fin n → ℤ) := outputProb H (dgsInput B r 1 precision)
          (fun out => encVec encI z <+: out)
        HasSum draw 1 → ∀ event : (Fin count → Fin n → ℤ) → Prop,
          outputProb G (dgsInput B r count budget) (decodedPoolEvent event) =
            ∑' pool : Fin count → Fin n → ℤ,
              (∏ i, draw (pool i)) * (if event pool then 1 else 0) := by
  classical
  obtain ⟨G,hG,hraw⟩ := uniform_raw_repetitions H hH requestWord countWord pack
    requestWord_poly countWord_poly pack_poly
  refine ⟨G,hG,?_⟩
  intro n B r count budget
  dsimp only
  intro _ event
  let input := dgsInput B r count budget
  let q := dgsInput B r 1 (count * (budget + 1))
  let Y := Bits (q.length + (H.anc q.length + 1))
  let raw (y : Y) : Str := List.ofFn fun j => y (H.outW q.length j)
  let mass (y : Y) : ℝ := ‖runLayered (H.circ q.length) (basisInput (toBits q)) y‖ ^ 2
  let R (y : Y) (z : Fin n → ℤ) : Prop := encVec encI z <+: raw y
  have hu (y : Y) (a b : Fin n → ℤ) : R y a → R y b → a = b :=
    fun ha hb => row_unique ha hb
  rw [hraw input q count (requestWord_dgs B r count budget) (countWord_dgs B r count budget)
    (decodedPoolEvent event)]
  refine Eq.trans (Finset.sum_congr rfl (fun ys _ => ?_)) (group_records count mass R hu event)
  change (∏ i, mass (ys i)) * (if decodedPoolEvent event
    (pack (List.ofFn (fun i => raw (ys i))) ++ _) then 1 else 0) =
    (∏ i, mass (ys i)) * (if ∃ zs, (∀ i, R (ys i) (zs i)) ∧ event zs then 1 else 0)
  simp only [decodedPoolEvent,pack_prefix,R]
