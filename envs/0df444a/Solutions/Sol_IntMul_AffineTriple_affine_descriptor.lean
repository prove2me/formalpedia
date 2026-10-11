-- Prove2me | solution 1 for IntMul.AffineTriple.affine_descriptor
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-10T15:57:24.535975+00:00
-- url     : https://prove2.me/submissions/36916cab-6902-495e-981f-50c7efe1c38b

import Definitions.Def_IntMul_AffineTriple
import Mathlib.Tactic

set_option maxHeartbeats 1000000
set_option Elab.async false

namespace IntMul.AffineTriple

private theorem triple_value (c : Fin 3) (bs : List Bool) :
    BinaryAdder.littleVal (triple c bs)=3*BinaryAdder.littleVal bs+c.val := by
  induction bs generalizing c with
  | nil => fin_cases c <;> simp [triple,BinaryAdder.littleVal]
  | cons b bs ih =>
      simp only [triple,BinaryAdder.littleVal,ih]
      fin_cases c <;> cases b <;> simp [digit,nextCarry] <;> omega

private theorem triple_length (c : Fin 3) (bs : List Bool) : (triple c bs).length≤ bs.length+2 := by
  induction bs generalizing c with
  | nil => fin_cases c <;> simp [triple]
  | cons b bs ih => simp only [triple,List.length_cons];have h := ih (nextCarry c b);omega

private theorem owned_intmulaffinetriplenumeric_foldl_affine (x : List Bool) (a : ℕ) :
    x.foldl (fun acc b => 2*acc+b.toNat) a=2^x.length*a+val x := by
  induction x generalizing a with
  | nil => simp [val]
  | cons b xs ih =>
      simp only [List.foldl_cons,List.length_cons];rw [ih]
      have hv : val (b::xs)=2^xs.length*b.toNat+val xs := by
        simp only [val,List.foldl_cons,Nat.mul_zero,Nat.zero_add];exact ih b.toNat
      rw [hv,pow_succ];ring
private theorem owned_intmulaffinetriplenumeric_val_append (x y : List Bool) : val (x++y)=2^y.length*val x+val y := by
  unfold val;rw [List.foldl_append];exact owned_intmulaffinetriplenumeric_foldl_affine y _
private theorem owned_intmulaffinetriplenumeric_val_singleton (b : Bool) : val [b]=b.toNat := by simp [val]
private theorem val_reverse_little (x : List Bool) : val x.reverse=BinaryAdder.littleVal x := by
  induction x with
  | nil => simp [val,BinaryAdder.littleVal]
  | cons b xs ih =>
      rw [List.reverse_cons,owned_intmulaffinetriplenumeric_val_append,owned_intmulaffinetriplenumeric_val_singleton]
      simp only [List.length_singleton,pow_one,ih,BinaryAdder.littleVal];ring

private theorem little_reverse_val (w : List Bool) : BinaryAdder.littleVal w.reverse=val w := by
  rw [←val_reverse_little,List.reverse_reverse]
end IntMul.AffineTriple

namespace IntMul.AffineTriple
open TapeCopy (Sym)

private theorem cfg_ext (c d : machine.Cfg)
    (hs : c.state=d.state) (hc : c.cells=d.cells) (hh : c.head=d.head) : c=d := by
  cases c;cases d;cases hs;cases hc;cases hh;rfl

private def seekFrame (w : List Bool) (j : ℕ) : machine.Cfg where
  state := .seek
  cells := (initialFrame w).cells
  head := fun i => if i=0 then j+1 else if i=1 then 1 else 0

private def calcFrame (done bs out : List Bool) (c : Fin 3) : machine.Cfg where
  state := .calc c
  cells := fun i => if i=0 then machine.tapeOf ((done++bs).reverse.map machine.bitSym)
    else if i=1 then machine.tapeOf (out.map machine.bitSym) else machine.tapeOf []
  head := fun i => if i=0 then bs.length else if i=1 then out.length+1 else 0

private def calcDone (done bs out : List Bool) (c : Fin 3) : machine.Cfg where
  state := .halt
  cells := fun i => if i=0 then machine.tapeOf ((done++bs).reverse.map machine.bitSym)
    else if i=1 then machine.tapeOf ((out++triple c bs).map machine.bitSym) else machine.tapeOf []
  head := fun i => if i=1 then (out++triple c bs).length+1 else 0

private def emitFrame (done out : List Bool) : machine.Cfg where
  state := .emit
  cells := fun i => if i=0 then machine.tapeOf (done.reverse.map machine.bitSym)
    else if i=1 then machine.tapeOf (out.map machine.bitSym) else machine.tapeOf []
  head := fun i => if i=1 then out.length+1 else 0

end IntMul.AffineTriple

namespace IntMul.AffineTriple
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem bits_read (w : List Bool) (j : ℕ) (hj : j< w.length) :
    machine.tapeOf (w.map machine.bitSym) (j+1)=machine.bitSym w[j] := by
  change (w.map machine.bitSym).getD j Sym.blank=_
  rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
private theorem bits_blank (w : List Bool) :
    machine.tapeOf (w.map machine.bitSym) (w.length+1)=Sym.blank := by
  change (w.map machine.bitSym).getD w.length Sym.blank=Sym.blank
  exact List.getD_eq_default _ _ (by simp)
private theorem bit_not_start (b : Bool) : machine.bitSym b≠Sym.start := by cases b <;> decide

private theorem tape_append_one (w : List Sym) (a : Sym) :
    Function.update (machine.tapeOf w) (w.length+1) a=machine.tapeOf (w++[a]) := by
  funext p
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
      by_cases hp : p=w.length
      · subst p;simp [MultitapeTM.tapeOf]
      · rw [Function.update_of_ne (by omega : p+1≠w.length+1)]
        simp only [MultitapeTM.tapeOf]
        by_cases hlt : p< w.length
        · rw [List.getD_append _ _ _ _ hlt]
        · have hge : w.length≤ p := by omega
          rw [List.getD_eq_default _ _ hge,List.getD_append_right _ _ _ _ hge]
          exact (List.getD_eq_default _ _ (by simp;omega)).symm

private theorem calc_source (done bs out : List Bool) (c : Fin 3) (b : Bool) :
    (calcFrame done (b::bs) out c).cells 0 ((calcFrame done (b::bs) out c).head 0)=machine.bitSym b := by
  change machine.tapeOf ((done++b::bs).reverse.map machine.bitSym) (bs.length+1)=_
  simp only [List.reverse_append,List.reverse_cons,List.map_append,List.map_singleton]
  change ((bs.reverse.map machine.bitSym++[machine.bitSym b])++done.reverse.map machine.bitSym).getD bs.length Sym.blank=_
  rw [List.append_assoc,List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem safe_right (s : Sym) : safeStep s s .right=(s,.right) := by
  by_cases hs : s=Sym.start <;> simp [safeStep,hs]
private theorem safe_left (s : Sym) (hs : s≠Sym.start) : safeStep s s .left=(s,.left) := by simp [safeStep,hs]
private theorem safe_blank_bit (b : Bool) : safeStep Sym.blank (machine.bitSym b) .right=(machine.bitSym b,.right) := by
  cases b <;> rfl
end IntMul.AffineTriple

namespace IntMul.AffineTriple
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem calc_bit_transition (c : Fin 3) (b : Bool) (a : Fin 3 → Sym)
    (hi : a 0=machine.bitSym b) (ho : a 1=Sym.blank) :
    transition (.calc c) a=(.calc (nextCarry c b),fun i =>
      (if i=1 then machine.bitSym (digit c b) else a i,
        if i=0 then Move.left else if i=1 then Move.right else Move.stay)) := by
  have hr : rawTransition (.calc c) a=(.calc (nextCarry c b),bitAction a c b) := by
    cases b <;> simp [rawTransition,hi,MultitapeTM.bitSym]
  simp only [transition,hr]
  congr 1
  funext i
  fin_cases i
  · exact safe_left _ (by change a 0≠Sym.start;rw [hi];exact bit_not_start b)
  · change safeStep (a 1) (machine.bitSym (digit c b)) .right=_
    rw [ho];exact safe_blank_bit _
  · exact safe_stay _

private theorem calc_bit_step (done bs out : List Bool) (c : Fin 3) (b : Bool) :
    machine.step (calcFrame done (b::bs) out c)=
      calcFrame (done++[b]) bs (out++[digit c b]) (nextCarry c b) := by
  have hi := calc_source done bs out c b
  have ho : (calcFrame done (b::bs) out c).cells 1 ((calcFrame done (b::bs) out c).head 1)=Sym.blank := bits_blank out
  have ht := calc_bit_transition c b (fun i => (calcFrame done (b::bs) out c).cells i
    ((calcFrame done (b::bs) out c).head i)) hi ho
  change transition (calcFrame done (b::bs) out c).state
    (fun i => (calcFrame done (b::bs) out c).cells i ((calcFrame done (b::bs) out c).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i
    · change Function.update ((calcFrame done (b::bs) out c).cells 0)
        ((calcFrame done (b::bs) out c).head 0)
        ((calcFrame done (b::bs) out c).cells 0 ((calcFrame done (b::bs) out c).head 0))=_
      rw [Function.update_eq_self]
      simp [calcFrame,List.append_assoc]
    · change Function.update (machine.tapeOf (out.map machine.bitSym)) (out.length+1)
        (machine.bitSym (digit c b))=machine.tapeOf ((out++[digit c b]).map machine.bitSym)
      simpa only [List.length_map,List.map_append,List.map_singleton] using
        tape_append_one (out.map machine.bitSym) (machine.bitSym (digit c b))
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht]
    funext i
    fin_cases i <;> simp [calcFrame,Nat.add_assoc]
end IntMul.AffineTriple

namespace IntMul.AffineTriple
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem owned_intmulaffinetripleflush_marker_transition (c : Fin 3) (a : Fin 3 → Sym)
    (hi : a 0=Sym.start) (ho : a 1=Sym.blank) :
    transition (.calc c) a=(if c=2 then .emit else .halt,fun i =>
      (if i=1 ∧ c≠0 then if c=1 then Sym.one else Sym.zero else a i,
        if i=1 ∧ c≠0 then Move.right else Move.stay)) := by
  fin_cases c <;> apply Prod.ext <;> simp [transition,rawTransition,hi]
  all_goals funext i;fin_cases i <;> simp [ho,safeStep,hi]
  all_goals intro h;exact h.symm

private theorem owned_intmulaffinetripleflush_marker_step (done out : List Bool) (c : Fin 3) :
    machine.step (calcFrame done [] out c)=
      if c=2 then emitFrame done (out++[false]) else calcDone done [] out c := by
  have hi : (calcFrame done [] out c).cells 0 ((calcFrame done [] out c).head 0)=Sym.start := rfl
  have ho : (calcFrame done [] out c).cells 1 ((calcFrame done [] out c).head 1)=Sym.blank := bits_blank out
  have ht := owned_intmulaffinetripleflush_marker_transition c (fun i => (calcFrame done [] out c).cells i
    ((calcFrame done [] out c).head i)) hi ho
  change transition (calcFrame done [] out c).state
    (fun i => (calcFrame done [] out c).cells i ((calcFrame done [] out c).head i))=_ at ht
  fin_cases c
  all_goals apply cfg_ext
  all_goals first
    | (simp only [MultitapeTM.step,ht];rfl)
    | (simp only [MultitapeTM.step,ht];funext i;fin_cases i)
  all_goals try (rw [Function.update_eq_self];simp [calcFrame,calcDone,emitFrame,triple])
  all_goals try rfl
  all_goals try (simpa [calcFrame,calcDone,emitFrame,triple,MultitapeTM.bitSym] using
    tape_append_one (out.map machine.bitSym) Sym.one)
  all_goals try (simpa [calcFrame,calcDone,emitFrame,triple,MultitapeTM.bitSym] using
    tape_append_one (out.map machine.bitSym) Sym.zero)
  all_goals simp [calcFrame,calcDone,emitFrame,triple,Nat.add_assoc]

private theorem owned_intmulaffinetripleflush_emit_step (done out : List Bool) :
    machine.step (emitFrame done out)=calcDone done [] (out++[true]) 0 := by
  have ho : (emitFrame done out).cells 1 ((emitFrame done out).head 1)=Sym.blank := bits_blank out
  have ht : transition .emit (fun i => (emitFrame done out).cells i ((emitFrame done out).head i))=
      (.halt,fun i => (if i=1 then Sym.one else (emitFrame done out).cells i ((emitFrame done out).head i),
        if i=1 then Move.right else Move.stay)) := by
    simp only [transition,rawTransition]
    congr 1;funext i;fin_cases i
    · exact safe_stay _
    · change safeStep ((emitFrame done out).cells 1 ((emitFrame done out).head 1)) Sym.one .right=_
      rw [ho];rfl
    · exact safe_stay _
  change transition (emitFrame done out).state
    (fun i => (emitFrame done out).cells i ((emitFrame done out).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i;fin_cases i
    · change Function.update ((emitFrame done out).cells 0) 0 ((emitFrame done out).cells 0 0)=_
      rw [Function.update_eq_self];simp [calcDone,emitFrame,triple]
    · simpa [calcDone,emitFrame,triple,MultitapeTM.bitSym] using tape_append_one (out.map machine.bitSym) Sym.one
    · exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];funext i;fin_cases i <;> simp [calcDone,emitFrame,triple,Nat.add_assoc]

private theorem calc_empty (done out : List Bool) (c : Fin 3) :
    ∃ t : ℕ, t≤ 2 ∧ machine.step^[t] (calcFrame done [] out c)=calcDone done [] out c := by
  by_cases hc : c=2
  · subst c
    refine ⟨2,by omega,?_⟩
    change machine.step (machine.step (calcFrame done [] out 2))=_
    rw [owned_intmulaffinetripleflush_marker_step,if_pos rfl,owned_intmulaffinetripleflush_emit_step]
    apply cfg_ext
    · rfl
    · funext i;fin_cases i <;> simp [calcDone,triple,List.append_assoc]
    · funext i;fin_cases i <;> simp [calcDone,triple]
  · refine ⟨1,by omega,?_⟩
    rw [Function.iterate_one,owned_intmulaffinetripleflush_marker_step,if_neg hc]
end IntMul.AffineTriple

namespace IntMul.AffineTriple

private theorem calc_complete (done bs out : List Bool) (c : Fin 3) :
    ∃ t : ℕ, t≤ bs.length+2 ∧ machine.step^[t] (calcFrame done bs out c)=calcDone done bs out c := by
  induction bs generalizing done out c with
  | nil => exact calc_empty done out c
  | cons b bs ih =>
      obtain ⟨t,ht,he⟩ := ih (done++[b]) (out++[digit c b]) (nextCarry c b)
      have hf : calcDone (done++[b]) bs (out++[digit c b]) (nextCarry c b)=calcDone done (b::bs) out c := by
        apply cfg_ext
        · rfl
        · funext i;fin_cases i <;> simp [calcDone,triple,List.append_assoc]
        · funext i;fin_cases i <;> simp [calcDone,triple,List.append_assoc,Nat.add_assoc]
      refine ⟨t+1,by simp only [List.length_cons];omega,?_⟩
      rw [Function.iterate_succ_apply,calc_bit_step,he,hf]
end IntMul.AffineTriple

namespace IntMul.AffineTriple
open TapeCopy (Sym)
open TapeAdder (safeStep safe_stay)

private theorem open_step (w : List Bool) : machine.step (initialFrame w)=seekFrame w 0 := by
  have ht : transition (initialFrame w).state
      (fun i => (initialFrame w).cells i ((initialFrame w).head i))=
      (.seek,fun i => ((initialFrame w).cells i ((initialFrame w).head i),
        if i=0 ∨ i=1 then Move.right else Move.stay)) := by
    change transition .open _=_
    simp only [transition,rawTransition]
    congr 1;funext i;fin_cases i
    · exact safe_right _
    · exact safe_right _
    · exact safe_stay _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i
    exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];funext i;fin_cases i <;> rfl

private theorem seek_bit_transition (a : Fin 3 → Sym) (b : Bool) (hi : a 0=machine.bitSym b) :
    transition .seek a=(.seek,fun i => (a i,if i=0 then Move.right else Move.stay)) := by
  have hr : rawTransition .seek a=(.seek,fun i => (a i,if i=0 then Move.right else Move.stay)) := by
    cases b <;> simp [rawTransition,hi,MultitapeTM.bitSym]
  simp only [transition,hr]
  congr 1;funext i;fin_cases i
  · exact safe_right _
  · exact safe_stay _
  · exact safe_stay _

private theorem seek_bit_step (w : List Bool) (j : ℕ) (hj : j< w.length) :
    machine.step (seekFrame w j)=seekFrame w (j+1) := by
  have hi : (seekFrame w j).cells 0 ((seekFrame w j).head 0)=machine.bitSym w[j] := bits_read w j hj
  have ht := seek_bit_transition (fun i => (seekFrame w j).cells i ((seekFrame w j).head i)) w[j] hi
  change transition (seekFrame w j).state (fun i => (seekFrame w j).cells i ((seekFrame w j).head i))=_ at ht
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i;exact Function.update_eq_self _ _
  · simp only [MultitapeTM.step,ht];funext i;fin_cases i <;> simp [seekFrame,Nat.add_assoc]

private theorem seek_run (w : List Bool) (j : ℕ) (hj : j≤ w.length) :
    machine.step^[j] (seekFrame w 0)=seekFrame w j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply',ih (by omega),seek_bit_step w j (by omega)]

private theorem seek_turn (w : List Bool) :
    machine.step (seekFrame w w.length)=calcFrame [] w.reverse [] 2 := by
  have hi : (seekFrame w w.length).cells 0 ((seekFrame w w.length).head 0)=Sym.blank := bits_blank w
  have ht : transition (seekFrame w w.length).state
      (fun i => (seekFrame w w.length).cells i ((seekFrame w w.length).head i))=
      (.calc 2,fun i => ((seekFrame w w.length).cells i ((seekFrame w w.length).head i),
        if i=0 then Move.left else Move.stay)) := by
    change transition .seek _=_
    simp only [transition,rawTransition,hi]
    congr 1;funext i;fin_cases i
    · apply safe_left
      change (seekFrame w w.length).cells 0 ((seekFrame w w.length).head 0)≠Sym.start
      rw [hi];decide
    · exact safe_stay _
    · exact safe_stay _
  apply cfg_ext
  · simp only [MultitapeTM.step,ht];rfl
  · simp only [MultitapeTM.step,ht];funext i
    rw [Function.update_eq_self]
    fin_cases i <;> simp [seekFrame,initialFrame,calcFrame]
  · simp only [MultitapeTM.step,ht];funext i;fin_cases i <;> simp [seekFrame,calcFrame]
end IntMul.AffineTriple

namespace IntMul.AffineTriple

private theorem affine_descriptor (w : List Bool) :
    ∃ t : ℕ, t≤ 2*w.length+4 ∧ machine.step^[t] (initialFrame w)=finalFrame w ∧
      BinaryAdder.littleVal (triple 2 w.reverse)=3*val w+2 ∧
      (triple 2 w.reverse).length≤ w.length+2 := by
  obtain ⟨t,ht,he⟩ := calc_complete [] w.reverse [] 2
  have hs : machine.step^[w.length+2] (initialFrame w)=calcFrame [] w.reverse [] 2 := by
    calc
      machine.step^[w.length+2] (initialFrame w)=
          machine.step (machine.step^[w.length] (machine.step (initialFrame w))) := by
        rw [show w.length+2=(w.length+1)+1 by omega,Function.iterate_succ_apply,
          Function.iterate_succ_apply']
      _=calcFrame [] w.reverse [] 2 := by rw [open_step,seek_run w w.length le_rfl,seek_turn]
  have hf : calcDone [] w.reverse [] 2=finalFrame w := by
    apply cfg_ext
    · rfl
    · funext i;fin_cases i <;> simp [calcDone,finalFrame]
    · funext i;fin_cases i <;> simp [calcDone,finalFrame]
  refine ⟨t+(w.length+2),by simp only [List.length_reverse] at ht;omega,?_,?_,?_⟩
  · rw [Function.iterate_add_apply,hs,he,hf]
  · rw [triple_value,little_reverse_val];rfl
  · simpa using triple_length (2 : Fin 3) w.reverse
end IntMul.AffineTriple


open IntMul IntMul.AffineTriple

theorem solution (w : List Bool) :
    ∃ t : ℕ, t≤ 2*w.length+4 ∧ machine.step^[t] (initialFrame w)=finalFrame w ∧
      BinaryAdder.littleVal (triple 2 w.reverse)=3*val w+2 ∧
      (triple 2 w.reverse).length≤ w.length+2 :=
  IntMul.AffineTriple.affine_descriptor w

#print axioms solution
