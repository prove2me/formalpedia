-- Prove2me | solution 1 for IntMul.CarryBatch.carry_batch
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T12:59:34.816709+00:00
-- url     : https://prove2.me/submissions/bd5963f7-bc32-48ca-82f1-2365def70075

import Definitions.Def_IntMul_CarryBatch
import Mathlib.Tactic
import Theorems.Thm_IntMul_FiniteCaller_simulate_run
import Theorems.Thm_IntMul_ReusableCarryStep_reusable_carry_step
import Definitions.Def_IntMul_BinaryAdder
import Definitions.Def_IntMul_MultitapeModel
import Mathlib.Data.Nat.Bits
import Definitions.Def_IntMul_CarryNormalization
import Theorems.Thm_IntMul_PaddedCarryStep_padded_carry_step

set_option maxHeartbeats 1000000
set_option Elab.async false


namespace IntMul.CarryBatch
open TapeCopy (Sym)

private theorem cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

/-- Only the start state was changed. Every physical table action and the
configuration's full state, cells and heads are retained identically. -/
private noncomputable def calcView (c : ReusableCarryStep.machine.Cfg) : subroutine.Cfg where
  state := c.state
  cells := c.cells
  head := c.head

private theorem calc_step (c : ReusableCarryStep.machine.Cfg) :
    subroutine.step (calcView c)=calcView (ReusableCarryStep.machine.step c) := rfl

private theorem calc_run (c : ReusableCarryStep.machine.Cfg) (t : ℕ) :
    subroutine.step^[t] (calcView c)=calcView (ReusableCarryStep.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,calc_step,Function.iterate_succ_apply']

end IntMul.CarryBatch



namespace IntMul.CarryBatch
open TapeCopy (Sym)

private noncomputable def entryFrame (pre : List Bool) (xs : List (List Bool))
    (a y z l : List Bool) : machine.Cfg where
  state := if xs=[] then none else some ((),ReusableCarryStep.machine.qStart)
  cells := (initialFrame pre xs a y z l).cells
  head := (initialFrame pre xs a y z l).head

private noncomputable def checkFrame (pre : List Bool) (xs : List (List Bool))
    (a y z l : List Bool) : subroutine.Cfg where
  state := subroutine.qStart
  cells := (initialFrame pre xs a y z l).cells
  head := (initialFrame pre xs a y z l).head

private noncomputable def checkDone (pre : List Bool) (xs : List (List Bool))
    (a y z l : List Bool) : subroutine.Cfg :=
  {checkFrame pre xs a y z l with state := none}

private theorem root_read (pre rest l : List Bool) (j : ℕ) (hj : j < rest.length) :
    StreamCarryStep.rootTape pre [] rest l (pre.length+j+1)=subroutine.bitSym rest[j] := by
  change (((pre++[]++rest).map subroutine.bitSym++Sym.sep::l.map subroutine.bitSym).getD
    (pre.length+j) Sym.blank)=_
  simp only [List.append_nil,List.map_append,List.append_assoc]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_map]
  rw [show pre.length+j-pre.length=j by omega]
  rw [List.getD_append _ _ _ _ (by simpa using hj),
    List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]

private theorem root_end (pre l : List Bool) :
    StreamCarryStep.rootTape pre [] [] l (pre.length+1)=Sym.sep := by
  change (((pre++[]++[]).map subroutine.bitSym++Sym.sep::l.map subroutine.bitSym).getD
    pre.length Sym.blank)=_
  simp only [List.append_nil]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem root_bit (pre x tail l : List Bool) (hn : 0 < x.length) :
    StreamCarryStep.rootTape pre [] (x++tail) l (pre.length+1)=Sym.zero ∨
      StreamCarryStep.rootTape pre [] (x++tail) l (pre.length+1)=Sym.one := by
  have h0 : 0 < (x++tail).length := by simp;omega
  have hr := root_read pre (x++tail) l 0 h0
  simp only [Nat.add_zero] at hr
  rw [hr]
  cases (x++tail)[0]'h0 <;> decide

private theorem entry_native (pre x : List Bool) (xs : List (List Bool)) (a y z l : List Bool) :
    entryFrame pre (x::xs) a y z l=
      FiniteCaller.embed subroutine Unit () () dispatch
        (calcView (ReusableCarryStep.initialFrame pre x xs.flatten a y z l)) := by
  apply cfg_ext
  · simp only [entryFrame,FiniteCaller.embed,calcView,List.cons_ne_nil,if_false]
    rfl
  · funext i
    fin_cases i <;> simp [entryFrame,initialFrame,ReusableCarryStep.initialFrame,
      StreamCarryStep.initialFrame,StreamCarryStep.rootTape,List.append_assoc] <;> rfl
  · rfl

private theorem entry_empty (pre a y z l : List Bool) :
    entryFrame pre [] a y z l=finalFrame pre [] a y z l := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [entryFrame,initialFrame,StreamCarryStep.initialFrame,finalFrame,scanWords] <;> rfl
  · funext i
    fin_cases i <;> simp [entryFrame,initialFrame,StreamCarryStep.initialFrame,finalFrame,scanWords]

private theorem setup_initial (pre : List Bool) (xs : List (List Bool)) (a y z l : List Bool) :
    initialFrame pre xs a y z l=
      FiniteCaller.embed subroutine Unit () () dispatch (checkFrame pre xs a y z l) := rfl

end IntMul.CarryBatch



namespace IntMul.CarryBatch
open TapeCopy (Sym)

/-- The inherited descriptor-return state performs its actual halt at the
real marker. It freezes every prepared cell and head. -/
private noncomputable def checkInner (pre : List Bool) (xs : List (List Bool)) (a y z l : List Bool) :
    ReusableCarryStep.subroutine.Cfg where
  state := ReusableCarryStep.relayState .seekDescriptor
  cells := (initialFrame pre xs a y z l).cells
  head := (initialFrame pre xs a y z l).head

private noncomputable def checkInnerDone (pre : List Bool) (xs : List (List Bool)) (a y z l : List Bool) :
    ReusableCarryStep.subroutine.Cfg := {checkInner pre xs a y z l with state := none}

private theorem inner_check_step (pre : List Bool) (xs : List (List Bool)) (a y z l : List Bool) :
    ReusableCarryStep.subroutine.step (checkInner pre xs a y z l)=checkInnerDone pre xs a y z l := by
  let s : Fin 15 → Sym := fun i => (checkInner pre xs a y z l).cells i ((checkInner pre xs a y z l).head i)
  have hi : s 6=Sym.start := rfl
  have ht : ReusableCarryStep.transition (ReusableCarryStep.relayState .seekDescriptor) s=
      (none,fun i => (s i,Move.stay)) := by
    simp only [ReusableCarryStep.transition,ReusableCarryStep.rawTransition,
      ReusableCarryStep.relayState,ReusableCarryStep.relayRaw,if_pos hi]
    congr 1
    funext i
    exact TapeAdder.safe_stay _
  change ReusableCarryStep.transition (checkInner pre xs a y z l).state
    (fun i => (checkInner pre xs a y z l).cells i ((checkInner pre xs a y z l).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];rfl

private theorem check_complete (pre : List Bool) (xs : List (List Bool)) (a y z l : List Bool) :
    ∃ t : ℕ, t ≤ 2 ∧ subroutine.step^[t] (checkFrame pre xs a y z l)=checkDone pre xs a y z l := by
  obtain ⟨t,ht,he⟩ := (FiniteCaller.simulate_run ReusableCarryStep.subroutine ReusableCarryStep.Phase
    .calc .descriptor ReusableCarryStep.dispatch (checkInner pre xs a y z l) 1).2
      (by change (ReusableCarryStep.subroutine.step (checkInner pre xs a y z l)).state=none;rw [inner_check_step];rfl)
  change t ≤ 2 at ht
  change ReusableCarryStep.machine.step^[t]
      (FiniteCaller.embed ReusableCarryStep.subroutine ReusableCarryStep.Phase .calc .descriptor
        ReusableCarryStep.dispatch (checkInner pre xs a y z l))=
    FiniteCaller.returned ReusableCarryStep.subroutine ReusableCarryStep.Phase .calc .descriptor
      ReusableCarryStep.dispatch (ReusableCarryStep.subroutine.step (checkInner pre xs a y z l)) at he
  rw [inner_check_step] at he
  have hin : calcView (FiniteCaller.embed ReusableCarryStep.subroutine ReusableCarryStep.Phase
      .calc .descriptor ReusableCarryStep.dispatch (checkInner pre xs a y z l))=checkFrame pre xs a y z l := rfl
  have hout : calcView (FiniteCaller.returned ReusableCarryStep.subroutine ReusableCarryStep.Phase
      .calc .descriptor ReusableCarryStep.dispatch (checkInnerDone pre xs a y z l))=checkDone pre xs a y z l := rfl
  refine ⟨t,ht,?_⟩
  rw [←hin,calc_run,he,hout]

end IntMul.CarryBatch



namespace IntMul.CarryBatch
open TapeCopy (Sym)

/-- Exact ready cells and heads after a single update. The caller's real
return transition supplies the subsequent state change. -/
private theorem next_ready (pre x xNext tailNext a y z l : List Bool)
    (hB : CarryStep.blockSize z ≤ x.length+1) :
    (ReusableCarryStep.finalFrame pre x (xNext++tailNext) a y z l).cells=
      (ReusableCarryStep.initialFrame (pre++x) xNext tailNext (a++CarryStep.digitWord x y z)
        (PaddedCarryStep.nextCarryWord x y z) z l).cells ∧
    (ReusableCarryStep.finalFrame pre x (xNext++tailNext) a y z l).head=
      (ReusableCarryStep.initialFrame (pre++x) xNext tailNext (a++CarryStep.digitWord x y z)
        (PaddedCarryStep.nextCarryWord x y z) z l).head := by
  have hd : (CarryStep.digitWord x y z).length=CarryStep.blockSize z := by
    simp [CarryStep.digitWord,CarryStep.sumWord,bin,Nat.min_eq_left hB]
  constructor
  · funext i
    fin_cases i <;> simp [ReusableCarryStep.finalFrame,ReusableCarryStep.initialFrame,
      StreamCarryStep.initialFrame,StreamCarryStep.rootTape,List.append_assoc] <;> rfl
  · funext i
    fin_cases i <;> simp [ReusableCarryStep.finalFrame,ReusableCarryStep.initialFrame,
      StreamCarryStep.initialFrame,hd,Nat.add_assoc]

private theorem after_setup (pre : List Bool) (xs : List (List Bool)) (a y z l : List Bool)
    (hn : ∀ w ∈ xs, 0 < w.length) :
    FiniteCaller.returned subroutine Unit () () dispatch (checkDone pre xs a y z l)=
      entryFrame pre xs a y z l := by
  apply cfg_ext
  · cases xs with
    | nil =>
      have hs : (checkDone pre [] a y z l).cells 0 ((checkDone pre [] a y z l).head 0)=Sym.sep :=
        root_end pre l
      simp only [FiniteCaller.returned,dispatch,hs,entryFrame,if_true]
      simp only [show ¬(Sym.sep=Sym.zero ∨ Sym.sep=Sym.one) by decide,if_false]
    | cons x xs =>
      have hx : 0 < x.length := hn x (by simp)
      have hs : (checkDone pre (x::xs) a y z l).cells 0 ((checkDone pre (x::xs) a y z l).head 0)=Sym.zero ∨
          (checkDone pre (x::xs) a y z l).cells 0 ((checkDone pre (x::xs) a y z l).head 0)=Sym.one :=
        root_bit pre x xs.flatten l hx
      simp [FiniteCaller.returned,dispatch,hs,entryFrame]
  · rfl
  · rfl

private theorem after_coefficient (pre x : List Bool) (xs : List (List Bool)) (a y z l : List Bool)
    (hB : CarryStep.blockSize z ≤ x.length+1) (hn : ∀ w ∈ xs, 0 < w.length) :
    FiniteCaller.returned subroutine Unit () () dispatch
      (calcView (ReusableCarryStep.finalFrame pre x xs.flatten a y z l))=
        entryFrame (pre++x) xs (a++CarryStep.digitWord x y z)
          (PaddedCarryStep.nextCarryWord x y z) z l := by
  have hready := next_ready pre x [] xs.flatten a y z l hB
  simp only [List.nil_append] at hready
  have hc := hready.1
  have hh := hready.2
  apply cfg_ext
  · have hs : (calcView (ReusableCarryStep.finalFrame pre x xs.flatten a y z l)).cells 0
        ((calcView (ReusableCarryStep.finalFrame pre x xs.flatten a y z l)).head 0)=
      StreamCarryStep.rootTape (pre++x) [] xs.flatten l ((pre++x).length+1) := by
      change (ReusableCarryStep.finalFrame pre x xs.flatten a y z l).cells 0
        ((ReusableCarryStep.finalFrame pre x xs.flatten a y z l).head 0)=_
      rw [hc,hh]
      rfl
    cases xs with
    | nil =>
      simp only [List.flatten_nil] at hs
      rw [root_end] at hs
      change dispatch () (fun i => (calcView (ReusableCarryStep.finalFrame pre x [].flatten a y z l)).cells i
        ((calcView (ReusableCarryStep.finalFrame pre x [].flatten a y z l)).head i))=none
      apply if_neg
      simp only [List.flatten_nil]
      rw [hs]
      decide
    | cons v vs =>
      have hv : 0 < v.length := hn v (by simp)
      have hb := root_bit (pre++x) v vs.flatten l hv
      simp only [List.flatten_cons] at hs
      have hbit : (calcView (ReusableCarryStep.finalFrame pre x (v::vs).flatten a y z l)).cells 0
          ((calcView (ReusableCarryStep.finalFrame pre x (v::vs).flatten a y z l)).head 0)=Sym.zero ∨
        (calcView (ReusableCarryStep.finalFrame pre x (v::vs).flatten a y z l)).cells 0
          ((calcView (ReusableCarryStep.finalFrame pre x (v::vs).flatten a y z l)).head 0)=Sym.one := by
        simp only [List.flatten_cons]
        rw [hs];exact hb
      change dispatch () (fun i => (calcView (ReusableCarryStep.finalFrame pre x (v::vs).flatten a y z l)).cells i
        ((calcView (ReusableCarryStep.finalFrame pre x (v::vs).flatten a y z l)).head i))=
          some ((),ReusableCarryStep.machine.qStart)
      exact if_pos hbit
  · exact hc
  · exact hh

private theorem final_cons (pre x : List Bool) (xs : List (List Bool)) (a y z l : List Bool) :
    finalFrame (pre++x) xs (a++CarryStep.digitWord x y z)
      (PaddedCarryStep.nextCarryWord x y z) z l=finalFrame pre (x::xs) a y z l := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [finalFrame,scanWords,StreamCarryStep.rootTape,List.append_assoc] <;> rfl
  · funext i
    fin_cases i <;> simp [finalFrame,scanWords,Nat.add_assoc]

end IntMul.CarryBatch



namespace IntMul.CarryBatch

private def updateBound (n : ℕ) (z l : List Bool) : ℕ :=
  41*n+13*CarryStep.blockSize z+21*z.length+4*l.length+126

/-- The induction follows the same fixed finite machine; every boundary
inspection and restart occurs in a real charged caller transition. -/
private theorem loop_complete (pre : List Bool) (xs : List (List Bool)) (a y z l : List Bool)
    (hy : y.length=val l+1) (hx : ∀ w ∈ xs, w.length=val l+1)
    (hB : CarryStep.blockSize z ≤ val l+2) :
    ∃ t : ℕ, t ≤ xs.length*updateBound (val l+1) z l ∧
      machine.step^[t] (entryFrame pre xs a y z l)=finalFrame pre xs a y z l := by
  induction xs generalizing pre a y with
  | nil => exact ⟨0,by simp,by simpa only [Function.iterate_zero_apply] using entry_empty pre a y z l⟩
  | cons x xs ih =>
    have hx0 : x.length=val l+1 := hx x (by simp)
    have hxt : ∀ w ∈ xs, w.length=val l+1 := by intro w hw;exact hx w (by simp [hw])
    obtain ⟨u,hu,he,hh,hd,hc⟩ := ReusableCarryStep.reusable_carry_step pre x xs.flatten a y z l
      (by omega) hx0 (by omega)
    have hnative : subroutine.step^[u] (calcView (ReusableCarryStep.initialFrame pre x xs.flatten a y z l))=
        calcView (ReusableCarryStep.finalFrame pre x xs.flatten a y z l) := by rw [calc_run,he]
    obtain ⟨s,hs,hstep⟩ := (FiniteCaller.simulate_run subroutine Unit () () dispatch
      (calcView (ReusableCarryStep.initialFrame pre x xs.flatten a y z l)) u).2 (by rw [hnative];rfl)
    rw [hnative,after_coefficient pre x xs a y z l (by omega)
      (by intro w hw;have hl := hxt w hw;omega)] at hstep
    have hcy : (PaddedCarryStep.nextCarryWord x y z).length=val l+1 := by
      simp [PaddedCarryStep.nextCarryWord,bin,hx0]
    obtain ⟨t,ht,htail⟩ := ih (pre++x) (a++CarryStep.digitWord x y z)
      (PaddedCarryStep.nextCarryWord x y z) hcy hxt
    have hfinal : machine.step^[t+s] (entryFrame pre (x::xs) a y z l)=finalFrame pre (x::xs) a y z l := by
      rw [Function.iterate_add_apply,entry_native,hstep,htail,final_cons]
    refine ⟨t+s,?_,hfinal⟩
    have hsbound : s ≤ updateBound (val l+1) z l := by unfold updateBound;omega
    simpa only [List.length_cons,Nat.succ_mul] using Nat.add_le_add ht hsbound

end IntMul.CarryBatch



namespace IntMul.CarryBatchEncoding
open IntMul.BinaryAdder (littleVal)

private theorem owned_intmulcarrybatchencoding_little_value_bound (x : List Bool) : littleVal x < 2 ^ x.length := by
  induction x with
  | nil => simp [littleVal]
  | cons b xs ih =>
      cases b <;> simp only [littleVal, List.length_cons, pow_succ,
        Bool.toNat_false, Bool.toNat_true] <;> omega

private theorem owned_intmulcarrybatchencoding_foldl_affine (x : List Bool) (a : ℕ) :
    x.foldl (fun acc b => 2 * acc + b.toNat) a = 2 ^ x.length * a + IntMul.val x := by
  induction x generalizing a with
  | nil => simp [IntMul.val]
  | cons b xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      have hv : IntMul.val (b :: xs) = 2 ^ xs.length * b.toNat + IntMul.val xs := by
        simp only [IntMul.val, List.foldl_cons, Nat.mul_zero, Nat.zero_add]
        exact ih b.toNat
      rw [hv, pow_succ]
      ring

private theorem owned_intmulcarrybatchencoding_val_append (x y : List Bool) :
    IntMul.val (x ++ y) = 2 ^ y.length * IntMul.val x + IntMul.val y := by
  unfold IntMul.val
  rw [List.foldl_append]
  exact owned_intmulcarrybatchencoding_foldl_affine y _

private theorem owned_intmulcarrybatchencoding_val_singleton (b : Bool) : IntMul.val [b] = b.toNat := by
  simp [IntMul.val]

private theorem owned_intmulcarrybatchencoding_val_reverse_little (x : List Bool) : IntMul.val x.reverse = littleVal x := by
  induction x with
  | nil => simp [IntMul.val, littleVal]
  | cons b xs ih =>
      rw [List.reverse_cons, owned_intmulcarrybatchencoding_val_append, owned_intmulcarrybatchencoding_val_singleton]
      simp only [List.length_singleton, pow_one, ih, littleVal]
      ring


private theorem owned_intmulcarrybatchencoding_little_value_test_bit (x : List Bool) (i : ℕ) :
    (littleVal x).testBit i = x.getD i false := by
  induction x generalizing i with
  | nil => simp [littleVal]
  | cons b xs ih =>
      have hv : littleVal (b :: xs) = Nat.bit b (littleVal xs) := by
        cases b <;> simp [littleVal, Nat.bit] <;> omega
      rw [hv]
      cases i with
      | zero => cases b <;> simp [Nat.bit, Nat.testBit_zero]
      | succ i => rw [Nat.testBit_bit_succ]; simpa using ih i

/-- The campaign's padded big-endian binary encoding returns every original
word, preserving its declared width and any leading zeroes. -/
private theorem bin_value_roundtrip (x : List Bool) : IntMul.bin x.length (IntMul.val x) = x := by
  have hv : IntMul.val x = littleVal x.reverse := by
    rw [← owned_intmulcarrybatchencoding_val_reverse_little, List.reverse_reverse]
  apply List.ext_getElem (by simp [IntMul.bin])
  intro i hi hx
  simp only [IntMul.bin, List.getElem_ofFn]
  rw [hv, owned_intmulcarrybatchencoding_little_value_test_bit]
  have hj : x.length - 1 - i < x.reverse.length := by simp only [List.length_reverse]; omega
  rw [List.getD_eq_getElem _ _ hj, List.getElem_reverse hj]
  have he : x.length - 1 - (x.length - 1 - i) = i := by omega
  simp only [he]


end IntMul.CarryBatchEncoding





namespace IntMul.CarryBatch

/-- The complete physical word traversal agrees with ordinary base-2^B carry
normalization, including padded zero digits and the exact retained carry. -/
private theorem numeric_scan (z : List Bool) (xs : List (List Bool)) (y : List Bool) (n : ℕ)
    (hy : y.length=n) (hx : ∀ w ∈ xs, w.length=n)
    (hB : CarryStep.blockSize z ≤ n+1) :
    (scanWords z xs y).1=
      (CarryNormalization.scan (2^CarryStep.blockSize z) (xs.map val) (val y)).1.flatMap
        (fun d => (bin (CarryStep.blockSize z) d).reverse) ∧
    val (scanWords z xs y).2=
      (CarryNormalization.scan (2^CarryStep.blockSize z) (xs.map val) (val y)).2 := by
  induction xs generalizing y with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    have hx0 : x.length=n := hx x (by simp)
    have hxt : ∀ w ∈ xs, w.length=n := by intro w hw;exact hx w (by simp [hw])
    obtain ⟨t,ht,he,hh,hd,hc⟩ := PaddedCarryStep.padded_carry_step x y z (by omega) (by omega)
    have hcy : (PaddedCarryStep.nextCarryWord x y z).length=n := by
      simp [PaddedCarryStep.nextCarryWord,bin,hx0]
    have hi := ih (PaddedCarryStep.nextCarryWord x y z) hcy hxt
    rw [hc] at hi
    have hdl : (CarryStep.digitWord x y z).length=CarryStep.blockSize z := by
      simp [CarryStep.digitWord,CarryStep.sumWord,bin,Nat.min_eq_left (by omega : CarryStep.blockSize z ≤ x.length+1)]
    have hr := CarryBatchEncoding.bin_value_roundtrip (CarryStep.digitWord x y z).reverse
    rw [List.length_reverse,hdl,hd] at hr
    have hw : CarryStep.digitWord x y z=(bin (CarryStep.blockSize z)
        ((val x+val y)%(2^CarryStep.blockSize z))).reverse := by
      simpa only [List.reverse_reverse] using (congrArg List.reverse hr).symm
    constructor
    · simpa only [scanWords,List.map_cons,CarryNormalization.scan,List.flatMap_cons,hw] using
        congrArg (fun w => CarryStep.digitWord x y z++w) hi.1
    · simpa only [scanWords,List.map_cons,CarryNormalization.scan] using hi.2

end IntMul.CarryBatch



namespace IntMul.CarryBatch

/-- One complete actual finite-state pass over a coefficient list. All loop
restarts, boundary inspections, workspace erasures and the empty-list halt
are counted; emitted bits and final carry agree with the mathematical scan. -/
private theorem carry_batch (pre : List Bool) (xs : List (List Bool)) (a y z l : List Bool)
    (hy : y.length=val l+1) (hx : ∀ w ∈ xs, w.length=val l+1)
    (hB : CarryStep.blockSize z ≤ val l+2) :
    ∃ t : ℕ, t ≤ xs.length*(41*(val l+1)+13*CarryStep.blockSize z+21*z.length+4*l.length+126)+3 ∧
      machine.step^[t] (initialFrame pre xs a y z l)=finalFrame pre xs a y z l ∧
      (machine.step^[t] (initialFrame pre xs a y z l)).state=machine.qHalt ∧
      (scanWords z xs y).1=
        (CarryNormalization.scan (2^CarryStep.blockSize z) (xs.map val) (val y)).1.flatMap
          (fun d => (bin (CarryStep.blockSize z) d).reverse) ∧
      val (scanWords z xs y).2=
        (CarryNormalization.scan (2^CarryStep.blockSize z) (xs.map val) (val y)).2 := by
  obtain ⟨u,hu,hcheck⟩ := check_complete pre xs a y z l
  obtain ⟨s,hs,hsetup⟩ := (FiniteCaller.simulate_run subroutine Unit () () dispatch
    (checkFrame pre xs a y z l) u).2 (by rw [hcheck];rfl)
  rw [hcheck,after_setup pre xs a y z l (by intro w hw;have hl := hx w hw;omega)] at hsetup
  obtain ⟨t,ht,hloop⟩ := loop_complete pre xs a y z l hy hx hB
  have he : machine.step^[t+s] (initialFrame pre xs a y z l)=finalFrame pre xs a y z l := by
    rw [Function.iterate_add_apply,setup_initial,hsetup,hloop]
  have hn := numeric_scan z xs y (val l+1) hy hx (by omega)
  refine ⟨t+s,?_,he,?_,hn.1,hn.2⟩
  · dsimp only [updateBound] at ht
    omega
  · rw [he];rfl

end IntMul.CarryBatch



open IntMul IntMul.CarryBatch

theorem solution (pre : List Bool) (xs : List (List Bool)) (a y z l : List Bool)
    (hy : y.length=val l+1) (hx : ∀ w ∈ xs, w.length=val l+1)
    (hB : CarryStep.blockSize z ≤ val l+2) :
    ∃ t : ℕ, t ≤ xs.length*(41*(val l+1)+13*CarryStep.blockSize z+21*z.length+4*l.length+126)+3 ∧
      machine.step^[t] (initialFrame pre xs a y z l)=finalFrame pre xs a y z l ∧
      (machine.step^[t] (initialFrame pre xs a y z l)).state=machine.qHalt ∧
      (scanWords z xs y).1=
        (CarryNormalization.scan (2^CarryStep.blockSize z) (xs.map val) (val y)).1.flatMap
          (fun d => (bin (CarryStep.blockSize z) d).reverse) ∧
      val (scanWords z xs y).2=
        (CarryNormalization.scan (2^CarryStep.blockSize z) (xs.map val) (val y)).2 :=
  IntMul.CarryBatch.carry_batch pre xs a y z l hy hx hB

#print axioms solution
