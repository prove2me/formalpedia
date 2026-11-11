-- Prove2me | solution 1 for OAI.UniformKServer.uniform_squared_logarithmic_main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:01:36.40087+00:00
-- url     : https://prove2.me/submissions/69d981a8-bcc3-47ce-be10-0d5a0c9be02b

import Mathlib
import Definitions.Def_UniformKServer
import Definitions.Def_Q220Uk008
import Theorems.Thm_OAI_UniformKServer_ConstructorSearch_exists_certificate
import Theorems.Thm_OAI_UniformKServer_RawControllerCost_delayed_bound
import Theorems.Thm_OAI_UniformKServer_UniformWrapper_all_reachable
import Theorems.Thm_OAI_UniformKServer_UniformWrapper_live_next
import Theorems.Thm_OAI_UniformKServer_UniformWrapper_prefix_expected

section
-- module Solutions.Q220_UK.UniformKServer_RawArithmetic
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

                                    
section

/-! A primitive-recursive nonnegative rational presentation for the uniform
finite certificate search. Denominators are stored minus one, so every bit
string denotes a valid nonnegative rational; there is no division oracle. -/
namespace UniformKServer.RawArithmetic

theorem eq_present (a : ℚ) (ha : 0≤a) : value (a.num.natAbs,a.den-1)=a := by
  have hd : a.den-1+1=a.den := by have:=a.pos; omega
  unfold value
  rw [←Nat.cast_one (R:=ℚ),←Nat.cast_add,hd]
  have hn : (a.num.natAbs:ℚ)=a.num := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℚ))
      (Int.natAbs_of_nonneg (Rat.num_nonneg.mpr ha))
  rw [hn,Rat.num_div_den]

open Primrec

end UniformKServer.RawArithmetic

end



end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawMetric
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.RawMetric
open RawArithmetic RawWords RawTable RawTyped RawCertificate

@[simp] theorem present_eq (a : ℚ) (ha : 0≤a) : value (present a)=a := eq_present a ha

end UniformKServer.RawMetric

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_OffsetInstance
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                     
section

/-! Uniform absolute squared-log cost for the exact rational-search/dyadic
suffix, with arbitrary repeated starts and arbitrary finite activation delay.
The literal bit-machine implementation is deliberately not asserted here. -/
namespace UniformKServer.OffsetInstance

open EffectiveLP ComputedInstance
variable (mult : ℕ) (hm : PartitionTree.absoluteRate ≤ (mult : ℝ))
variable {n k : ℕ} [NeZero k]

theorem coefficient_positive : 0 < coefficient mult := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold coefficient
  positivity

end UniformKServer.OffsetInstance

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawBinary
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.OffsetParameters.acceptableDecidable
attribute [-simp] _root_.OAI.UniformKServer.Fallback.mem_coverers _root_.OAI.UniformKServer.RawControl.initial_state _root_.OAI.UniformKServer.RawMarks.covers_bits _root_.OAI.UniformKServer.RawProgram.unpack_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.RawBinary
open Primrec RawCertificate
attribute [fun_prop] Primrec.list_tail

theorem value_bits (a : ℕ) : value a.bits=a := by
  induction a using Nat.binaryRec' with
  | zero=>rfl
  | bit b n h ih=>rw [Nat.bits_append_bit n b h,value_cons,ih]

@[simp] theorem read_natCode (a : ℕ) (w : List Bool) : readNat (natCode a++w)=(a,w) := by
  have ht : ((natCode a++w).takeWhile id).length=a.bits.length := by
    simp [natCode,List.append_assoc]
  dsimp only [readNat]
  rw [ht]
  have hd : (natCode a++w).drop (a.bits.length+1)=a.bits++w := by
    simp [natCode,List.append_assoc,List.drop_append]
  rw [hd]
  simp [value_bits]

@[simp] theorem read_rationalCode (a : ℚ) (w : List Bool) :
    readQ (rationalCode a++w)=(RawMetric.present a,w) := by
  simp only [readQ,rationalCode,List.cons_append,List.tail_cons,List.append_assoc,read_natCode,
    RawMetric.present]

theorem fold_read (xs : List ℚ) (w : List Bool) (ys : List RawArithmetic.Q) (m : ℕ) :
    (List.range' m xs.length).foldl (fun p _=>let a:=readQ p.2;(p.1++[a.1],a.2))
      (ys,(xs.map rationalCode).flatten++w)=(ys++xs.map RawMetric.present,w) := by
  induction xs generalizing ys m with
  | nil=>simp
  | cons x xs ih=>
    simp only [List.length_cons,List.range'_succ,List.map_cons,List.flatten_cons,
      List.append_assoc,List.foldl_cons,read_rationalCode]
    rw [ih]
    simp

theorem readMany_codes (xs : List ℚ) (w : List Bool) :
    readMany xs.length ((xs.map rationalCode).flatten++w)=(xs.map RawMetric.present,w) := by
  simpa only [readMany,List.range_eq_range',List.nil_append] using fold_read xs w [] 0

theorem distance_codes {n : ℕ} (d : RationalMetric n) :
    ((distances d).map rationalCode).flatten=
      (List.ofFn fun x : Fin n =>
        (List.ofFn fun y : Fin n => rationalCode (d.distance x y)).flatten).flatten := by
  simp only [distances,List.map_flatten,List.map_ofFn,Function.comp_def]
  rw [List.flatten_flatten]
  simp only [List.map_ofFn,Function.comp_def]

@[simp] theorem input_code {n k : ℕ} (d : RationalMetric n) (s : Configuration n k) :
    input (instanceCode d s)=(n,k,(distances d).map RawMetric.present) := by
  unfold input instanceCode
  simp only [List.append_assoc,read_natCode]
  rw [←distance_codes,←distances_length d,readMany_codes]

theorem distances_ofFn {n : ℕ} (d : RationalMetric n) :
    distances d=List.ofFn (fun z : Fin (n*n)=>
      d.distance (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2) := by
  rw [List.ofFn_mul]
  unfold distances
  congr 1
  apply List.ofFn_inj.mpr
  funext x
  apply List.ofFn_inj.mpr
  funext y
  have h : (⟨x.val*n+y.val,by nlinarith [x.isLt,y.isLt]⟩ : Fin (n*n))=finProdFinEquiv (x,y) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
  simp only [h,Equiv.symm_apply_apply]

theorem metric_input {n : ℕ} (d : RationalMetric n) (x y : Fin n) :
    RawArithmetic.value (RawTable.dist n ((distances d).map RawMetric.present) x.val y.val)=
      d.distance x y := by
  rw [distances_ofFn]
  simp only [List.map_ofFn,Function.comp_def,RawTable.dist]
  have hh : x.val*n+y.val<n*n := by nlinarith [x.isLt,y.isLt]
  rw [List.getD_eq_getElem _ _ (by simpa using hh)]
  simp only [List.getElem_ofFn]
  have h : (⟨x.val*n+y.val,hh⟩ : Fin (n*n))=finProdFinEquiv (x,y) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
  rw [h,Equiv.symm_apply_apply,RawMetric.present_eq _ (d.nonneg x y)]

end UniformKServer.RawBinary

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawBits
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                              
section

namespace UniformKServer.RawBits
open Primrec

 theorem bits_value (w : List Bool) : (RawBinary.value (w++[true])).bits=w++[true] := by
  induction w with
  | nil=>simp
  | cons b w ih=>
    simp only [List.cons_append,RawBinary.value_cons]
    rw [Nat.bits_append_bit _ _ (fun h=>by
      have hh:=congrArg Nat.bits h
      rw [ih] at hh
      simp at hh),ih]

open Turing.PartrecToTM2

end UniformKServer.RawBits

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StackTape
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions _root_.OAI.UniformKServer.StackCompiler.instFintypeHeadMove
attribute [-simp] _root_.OAI.UniformKServer.UniformWrapper.ofWord_tape _root_.OAI.UniformKServer.UniformWrapper.tape_shift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                
section

/-! A stack is physically stored at a tape head. Padding is literal blank
cells, not a unit-cost unbounded register. Each push/pop uses at most two
transitions. -/
namespace UniformKServer.StackTape

theorem head {s : List Bool} {t : BitTape} (h : Rep s t) : t.head=s.head? := by
  obtain ⟨l,r,rfl⟩:=h
  cases s <;> rfl

theorem blank : Rep [] BitTape.blank := ⟨0,0,rfl⟩

theorem push_rep (b : Bool) {s : List Bool} {t : BitTape} (h : Rep s t) :
    Rep (b::s) (push b t) := by
  obtain ⟨l,r,rfl⟩:=h
  cases s with
  | nil =>
    cases l with
    | zero => exact ⟨0,r+1,by simp [push,encode,BitTape.shift,List.replicate_succ]⟩
    | succ l => exact ⟨l,r+1,by simp [push,encode,BitTape.shift,List.replicate_succ]⟩
  | cons a s =>
    cases l with
    | zero => exact ⟨0,r,by simp [push,encode,BitTape.shift]⟩
    | succ l => exact ⟨l,r,by simp [push,encode,BitTape.shift,List.replicate_succ]⟩

theorem pop_rep {s : List Bool} {t : BitTape} (h : Rep s t) : Rep s.tail (pop t) := by
  obtain ⟨l,r,rfl⟩:=h
  cases s with
  | nil => exact ⟨l,r,by simp [pop,encode]⟩
  | cons b s =>
    cases s with
    | nil =>
      cases r with
      | zero => exact ⟨l+1,0,by simp [pop,encode,BitTape.shift,List.replicate_succ]⟩
      | succ r => exact ⟨l+1,r,by simp [pop,encode,BitTape.shift,List.replicate_succ]⟩
    | cons a s => exact ⟨l+1,r,by simp [pop,encode,BitTape.shift,List.replicate_succ]⟩

end UniformKServer.StackTape

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StackCompiler
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Finite-control, finite-alphabet stack processors, compiled to the exact
binary multitape model. There is no unit-cost arithmetic oracle. -/
namespace UniformKServer.StackCompiler
open scoped Classical

theorem decode_none (g : ℕ) : decode (fun _ : Fin g=>none)=none := by
  have hn : ¬∃ a : Fin g,∀j,(none : Option Bool)=some (code a j) := by
    rintro ⟨a,h⟩
    cases (h a)
  exact dite_eq_right hn

theorem decode_code {g : ℕ} (a : Fin g) : decode (fun j=>some (code a j))=some a := by
  unfold decode
  split_ifs with h
  · congr 1
    have he: code a a=code (Classical.choose h) a := Option.some.inj (Classical.choose_spec h a)
    exact of_decide_eq_true (he.symm.trans (by simp [code]))
  · exact False.elim (h ⟨a,fun _=>rfl⟩)

theorem matches_initial {q m g : ℕ} (P : Processor q m g) (input : List Bool) :
    Matches P (initial P input) ((machine P).initial input) :=
  ⟨rfl,rfl,rfl,rfl,fun _ _=>StackTape.blank⟩

theorem matches_heads {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (z : MachineState (machine P)) (h : Matches P s z) (i : Fin m) :
    decode (fun j=>(z.work (wire m g (i,j))).head)=(s.store i).head? := by
  have he : (fun j=>(z.work (wire m g (i,j))).head)=
      fun j=> ((s.store i).map (fun a=>code a j)).head? := funext (fun j=>StackTape.head (h.work i j))
  rw [he]
  cases hs:s.store i with
  | nil => exact decode_none _
  | cons a as => exact decode_code a

end UniformKServer.StackCompiler

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StackSimulation
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.UniformWrapper.ofWord_tape _root_.OAI.UniformKServer.UniformWrapper.tape_shift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.StackCompiler
open scoped Classical

private theorem write_none (t : BitTape) (ht : t.head=none) :
    {t with head:=none}=t := by
  cases t with
  | mk l h r =>
    change h=none at ht
    subst h
    rfl

theorem first_step {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (z : MachineState (machine P)) (h : Matches P s z) (hs : s.yielded=false) (coin : Bool) :
    (machine P).step z coin = middle P
      (P.transition s.control s.input.head (fun i=>(s.store i).head?) coin) z := by
  have hh : (fun i=>decode (fun j=>(z.work (wire m g (i,j))).head))=
      fun i=>(s.store i).head? := funext (matches_heads P s z h)
  simp only [BitMachine.step,h.yielded,hs,Bool.false_eq_true,↓reduceIte,
    machine,h.control,Equiv.symm_apply_apply,h.input,hh]
  unfold middle
  congr 1
  · rw [h.input]
  · funext v
    cases hp:(P.transition s.control s.input.head (fun i=>(s.store i).head?) coin).stackOp
        (((wire m g).symm v).1) with
    | keep => rfl
    | push a => rfl
    | pop =>
      simp only [beginOp,StackTape.pop]
      split_ifs with ht
      · simp only [BitTape.shift]
        exact write_none (z.work v) ht
      · rfl

theorem last_step {q m g : ℕ} (P : Processor q m g) (a : Action q m g)
    (z : MachineState (machine P)) (coin : Bool) :
    (machine P).step (middle P a z) coin = last P a (middle P a z) := by
  simp only [BitMachine.step,middle,Bool.false_eq_true,↓reduceIte,machine,
    Equiv.symm_apply_apply,last,BitTape.shift]
  congr 1
  funext v
  cases a.stackOp (((wire m g).symm v).1) <;> rfl

theorem op_rep {g : ℕ} (o : Op g) (j : Fin g) (l : List (Fin g)) (t : BitTape)
    (h : StackTape.Rep (l.map (fun a=>code a j)) t) :
    StackTape.Rep ((applyOp o l).map (fun a=>code a j)) (finishOp o j (beginOp o t)) := by
  cases o with
  | keep=>exact h
  | push a=>exact StackTape.push_rep (code a j) h
  | pop=>simpa only [applyOp,List.map_tail,beginOp,finishOp] using StackTape.pop_rep h

theorem matches_step {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (z : MachineState (machine P)) (h : Matches P s z) (coin unused : Bool) :
    Matches P (step P s coin) ((machine P).step ((machine P).step z coin) unused) := by
  cases hs:s.yielded with
  | true=> simpa [step,hs,BitMachine.step,h.yielded] using h
  | false=>
    rw [first_step P s z h hs,last_step]
    let a:=P.transition s.control s.input.head (fun i=>(s.store i).head?) coin
    change Matches P (step P s coin) (last P a (middle P a z))
    refine ⟨?_,?_,?_,?_,?_⟩
    · simp only [last,step,hs,Bool.false_eq_true,↓reduceIte]
      rfl
    · simp only [last,middle,step,hs,Bool.false_eq_true,↓reduceIte,h.input]
      rfl
    · simp only [last,middle,step,hs,Bool.false_eq_true,↓reduceIte,h.output]
      rfl
    · simp only [last,step,hs,Bool.false_eq_true,↓reduceIte]
      rfl
    · intro i j
      simpa only [last,middle,step,hs,Bool.false_eq_true,↓reduceIte,
        Equiv.symm_apply_apply] using op_rep (a.stackOp i) j (s.store i) _ (h.work i j)
end UniformKServer.StackCompiler

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_StackRun
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
attribute [-simp] _root_.OAI.UniformKServer.UniformWrapper.ofWord_tape _root_.OAI.UniformKServer.UniformWrapper.tape_shift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.StackCompiler

theorem matches_run {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (z : MachineState (machine P)) (h : Matches P s z) (bs : List Bool) :
    Matches P (run P s bs) ((machine P).run z (padded bs)) := by
  induction bs generalizing s z with
  | nil=>exact h
  | cons b bs ih=>
    exact ih _ _ (matches_step P s z h b false)

theorem padded_false (n : ℕ) : padded (List.replicate n false)=List.replicate (2*n) false := by
  induction n with
  | zero=>rfl
  | succ n ih=>simp [List.replicate_succ,padded,ih,Nat.mul_succ]

theorem matches_capped {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (z : MachineState (machine P)) (h : Matches P s z) (t : ℕ) :
    Matches P (run P s (List.replicate t false))
      ((machine P).run z (List.replicate (2*t) false)) := by
  simpa only [padded_false] using matches_run P s z h (List.replicate t false)

theorem run_halted {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    (hy : s.yielded=true) (bs : List Bool) : run P s bs=s := by
  induction bs with
  | nil=>rfl
  | cons b bs ih=>simpa [run_cons,step,hy] using ih

theorem capped_after {q m g : ℕ} (P : Processor q m g) (s : State q m g)
    {t B : ℕ} (h : (run P s (List.replicate t false)).yielded=true) (htB : t≤B) :
    run P s (List.replicate B false)=run P s (List.replicate t false) := by
  obtain ⟨a,rfl⟩:=Nat.exists_eq_add_of_le htB
  rw [List.replicate_add,run_append]
  exact run_halted P _ h _

end UniformKServer.StackCompiler

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_RawProgram
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
                                 
section

namespace UniformKServer.RawProgram
open Primrec RawCertificate
attribute [fun_prop] RawBits.primitive_bits

@[simp] theorem request_code (r : ℕ) :
    request (RawBinary.value (natCode (r+1)++[true]))=r := by
  simp only [request,RawBits.bits_value,RawBinary.read_natCode,Nat.add_sub_cancel]

end UniformKServer.RawProgram

end


end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ConstructorSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.ConstructorSearch
open RawCertificate
open scoped Classical

theorem terminates {mult : ℕ} {i : Input} (h : ∃v,verify mult i v=true) :
    (search mult i).Dom := by
  obtain ⟨v,hv⟩:=h
  apply Nat.rfindOpt_dom.mpr
  refine ⟨Encodable.encode v,v,?_⟩
  change v∈((Encodable.decode (Encodable.encode v) : Option Cert).bind _)
  rw [Encodable.encodek]
  simp only [Option.bind_some,hv,ite_true, if_true,Option.mem_some_iff]

theorem correct {mult : ℕ} {i : Input} {v : Cert} (h : v∈search mult i) :
    verify mult i v=true := by
  obtain ⟨a,ha⟩:=Nat.rfindOpt_spec h
  simp only [candidate,Option.mem_def,Option.bind_eq_some_iff] at ha
  obtain ⟨u,hu,hv⟩:=ha
  split at hv
  next h=>cases Option.some.inj hv;exact h
  next h=>simp at hv

end UniformKServer.ConstructorSearch

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_ConstructorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.ConstructorProgram
open RawCertificate
open scoped Classical

theorem code_correct {mult : ℕ} {a : ℕ} {v : ConstructorSearch.Cert}
    (h : v∈ConstructorSearch.search mult (read a)) :
    (result (read a) v).val∈Turing.ToPartrec.Code.eval (code mult) [a] := by
  exact Classical.choose_spec (LiteralVector.partial_code_exists (run mult) (run_partrec mult))
    (⟨[a],rfl⟩ : List.Vector ℕ 1) (result (read a) v) ((Part.mem_map_iff _).mpr ⟨v,h,rfl⟩)

theorem input_code {n k : ℕ} (d : RationalMetric n) (s : Configuration n k) (w : List Bool) :
    RawBinary.input (instanceCode d s++w)=(n,k,(RawBinary.distances d).map RawMetric.present) := by
  unfold RawBinary.input instanceCode
  simp only [List.append_assoc,RawBinary.read_natCode]
  rw [←RawBinary.distance_codes,←RawBinary.distances_length d,RawBinary.readMany_codes]

theorem read_code {n k : ℕ} (d : RationalMetric n) (s : Configuration n k) :
    read (RawBinary.value (instanceCode d s++[true]))=
      (n,k,(RawBinary.distances d).map RawMetric.present) := by
  rw [read,RawBits.bits_value,input_code]

end UniformKServer.ConstructorProgram

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_TypedStack
attribute [-instance] _root_.OAI.UniformKServer.LiteralPartrec.instFintypeK'_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.TypedStack
open StackCompiler
open scoped Classical

variable {Q K : Type*} {g : ℕ}

theorem encode_step [Fintype Q] [Fintype K] (P : Processor Q K g) (s : State Q K g) (b : Bool) :
    encode (step P s b)=StackCompiler.step (compile P) (encode s) b := by
  cases hy:s.yielded <;> simp only [step,StackCompiler.step,encode,compile,hy,
    Bool.false_eq_true,↓reduceIte,Equiv.symm_apply_apply]
  all_goals rfl

theorem encode_run [Fintype Q] [Fintype K] (P : Processor Q K g) (s : State Q K g) (bs : List Bool) :
    encode (run P s bs)=StackCompiler.run (compile P) (encode s) bs := by
  induction bs generalizing s with
  | nil=>rfl
  | cons b bs ih=>
    change encode (run P (step P s b) bs)=StackCompiler.run (compile P) (StackCompiler.step (compile P) (encode s) b) bs
    rw [ih,encode_step]

theorem encode_initial [Fintype Q] [Fintype K] (P : Processor Q K g) (w : List Bool) :
    encode (initial P w)=StackCompiler.initial (compile P) w := rfl

theorem run_cons (P : Processor Q K g) (s : State Q K g) (b : Bool) (bs : List Bool) :
    run P s (b::bs)=run P (step P s b) bs := rfl

theorem run_append (P : Processor Q K g) (s : State Q K g) (as bs : List Bool) :
    run P s (as++bs)=run P (run P s as) bs := List.foldl_append

theorem run_yielded (P : Processor Q K g) (s : State Q K g) (h : s.yielded=true) (bs : List Bool) :
    run P s bs=s := by
  induction bs with
  | nil=>rfl
  | cons b bs ih=>simpa only [run_cons,step,h,Bool.true_eq,↓reduceIte] using ih

end UniformKServer.TypedStack

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.TypedStack
variable {Q K : Type*} {g : ℕ}

theorem uniform_step (P : Processor Q K g) (s z : State Q K g) (h : ∀b,step P s b=z) :
    UniformRun P s 1 z := by
  intro bs hb
  cases bs with
  | nil=>simp at hb
  | cons b bs=>
    have he : bs=[]:=List.eq_nil_of_length_eq_zero (by simpa using hb)
    subst bs
    exact h b

theorem UniformRun.trans {P : Processor Q K g} {s z w : State Q K g} {t u : ℕ}
    (h : UniformRun P s t z) (h' : UniformRun P z u w) : UniformRun P s (t+u) w := by
  intro bs hb
  rw [←List.take_append_drop t bs,run_append,h (bs.take t) (by simp only [List.length_take,hb];omega)]
  exact h' _ (by simp only [List.length_drop,hb];omega)

theorem UniformRun.mono {P : Processor Q K g} {s z : State Q K g} {t u : ℕ}
    (h : UniformRun P s t z) (hy : z.yielded=true) (hu : t≤u) : UniformRun P s u z := by
  intro bs hb
  rw [←List.take_append_drop t bs,run_append,h (bs.take t) (by simp only [List.length_take,hb];omega)]
  exact run_yielded P z hy _

end UniformKServer.TypedStack

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}

variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

 theorem step_bootCons (i : BitTape) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .bootCons i [] [] []) coin=
      wordState .bootOne i [sep] [] [] := by
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

 theorem step_bootOne (i : BitTape) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .bootOne i [sep] [] []) coin=
      wordState .bootRead i [digit true,sep] [] [] := by
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

theorem read_step (q exit : Control qc qa)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=read q exit inp)
    (l : List (Option Bool)) (b : Bool) (w : List Bool) (m p buf : List (Fin g))
    (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState q (tape l (b::w)) m p buf out) coin=
      wordState q (tape (some b::l) w) m p (digit b::buf) out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,h,read,write]
  apply wordState_ext
  · rfl
  · exact tape_shift _ _ _
  · intro k;cases k with
    | base k=>cases k <;> rfl
    | pay=>rfl
    | buf=>rfl
  · rfl
  · rfl

theorem read_empty (q exit : Control qc qa)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=read q exit inp)
    (l : List (Option Bool)) (m p buf : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState q (tape l []) m p buf out) coin=
      wordState exit (tape l []) m p buf out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,h,read,pass,tape,BitTape.shift]
  rfl

theorem read_run (q exit : Control qc qa)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=read q exit inp)
    (l : List (Option Bool)) (w : List Bool) (m p buf : List (Fin g)) (out : List Bool) :
    UniformRun (processor C A) (wordState q (tape l w) m p buf out) (w.length+1)
      (wordState exit (tape (w.reverse.map some++l) []) m p ((w.map digit).reverse++buf) out) := by
  induction w generalizing l buf with
  | nil=>
    simpa only [List.length_nil,Nat.zero_add,List.reverse_nil,List.map_nil,List.nil_append] using
      uniform_step _ _ _ (read_empty C A q exit h l m p buf out)
  | cons b w ih=>
    have hs:=uniform_step _ _ _ (read_step C A q exit h l b w m p buf out)
    have hi:=ih (some b::l) (digit b::buf)
    convert hs.trans hi using 1 <;>
      (simp only [List.length_cons,List.reverse_cons,List.map_append,
        List.map_cons,List.append_assoc,List.singleton_append,List.map_nil]; try omega)

theorem buf_empty (q exit : Control qc qa) (y : Bool)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=
      match hd .buf with | none=>pass exit y | some a=>move q .buf main a)
    (i : BitTape) (m p : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState q i m p [] out) coin=
      wordState exit i m p [] out y := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,h,List.head?_nil,pass,BitTape.shift]
  rfl

theorem buf_run (q exit : Control qc qa) (y : Bool)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=
      match hd .buf with | none=>pass exit y | some a=>move q .buf main a)
    (i : BitTape) (xs m p : List (Fin g)) (out : List Bool) :
    UniformRun (processor C A) (wordState q i m p xs out) (xs.length+1)
      (wordState exit i (xs.reverse++m) p [] out y) := by
  induction xs generalizing m with
  | nil=>simpa only [List.length_nil,Nat.zero_add,List.reverse_nil,List.nil_append] using
      uniform_step _ _ _ (buf_empty C A q exit y h i m p out)
  | cons a xs ih=>
    have hs:=uniform_step _ _ _ (buf_step C A q exit y h i a xs m p out)
    convert hs.trans (ih (a::m)) using 1 <;>
      (simp only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append]; try omega)

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperBoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

 theorem initial_word (w : List Bool) :
    TypedStack.initial (processor C A) w=wordState .bootCons (tape [] w) [] [] [] := by
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

 theorem boot_run (w : List Bool) :
    UniformRun (processor C A) (TypedStack.initial (processor C A) w) (2*w.length+4)
      (wordState (.construct C.start) (tape (w.reverse.map some) [])
        (w.map digit++[digit true,sep]) [] [] [] true) := by
  rw [initial_word]
  have h₁:=uniform_step _ _ _ (step_bootCons C A (tape [] w))
  have h₂:=uniform_step _ _ _ (step_bootOne C A (tape [] w))
  have h₃:=read_run C A .bootRead .bootDrain (fun _ _ _=>rfl) [] w [digit true,sep] [] [] []
  have h₄:=buf_run C A .bootDrain (.construct C.start) true (fun _ _ _=>rfl)
    (tape (w.reverse.map some) []) (w.map digit).reverse [digit true,sep] [] []
  simp only [List.append_nil] at h₃
  simp only [List.reverse_reverse,List.length_reverse,List.length_map] at h₄
  have hh:=((h₁.trans h₂).trans h₃).trans h₄
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  omega

 theorem boot_word (w : List Bool) :
    (trList [RawBinary.value (w++[true])]).map FlatTM2.letters=
      w.map digit++[digit true,sep] := by
  simp only [trList,RawBits.trNat_bits,RawBits.bits_value,List.map_append,List.map_map,
    List.map_cons,List.map_nil]
  simp only [List.append_assoc,List.singleton_append]
  rfl

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.TypedStack
open scoped Classical
variable {Q K : Type*} [Fintype Q] [Fintype K] {g : ℕ}

 theorem CoreRep.yielded {P : Processor Q K g} {s : State Q K g}
    {z : MachineState (StackCompiler.machine (compile P))} (h : CoreRep P s z) : z.yielded=true := by
  obtain ⟨i,out,h⟩:=h
  exact h.yielded

 theorem matches_core {P : Processor Q K g} {s : State Q K g}
    {z : MachineState (StackCompiler.machine (compile P))}
    (h : StackCompiler.Matches (compile P) (encode s) z) (hy : s.yielded=true) : CoreRep P s z := by
  refine ⟨s.input,s.outputRev,?_⟩
  have he : frame s s.input s.outputRev=s := by cases s;simp_all only [frame]
  rw [he]
  exact h

end UniformKServer.TypedStack

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical

 theorem boot_core (mult : ℕ) {n k : ℕ} (d : RationalMetric n) (s : Configuration n k) :
    CoreRep (uniform mult)
      (wordState (.construct (literalC mult).start) BitTape.blank
        ((trList [RawBinary.value (instanceCode d s++[true])]).map FlatTM2.letters) [] [] [] true)
      (boot (machine mult) 64 1 d s) := by
  let P:=uniform mult
  let w:=instanceCode d s
  have hm:=StackCompiler.matches_capped (compile P) (StackCompiler.initial (compile P) w)
    ((StackCompiler.machine (compile P)).initial w) (StackCompiler.matches_initial _ _) (32*(w.length+1))
  rw [←encode_initial,←encode_run] at hm
  have hb:=boot_run (literalC mult) literalA w
  have he:=hb.mono rfl (show 2*w.length+4≤32*(w.length+1) by omega)
    (List.replicate (32*(w.length+1)) false) (by simp)
  change TypedStack.run P (TypedStack.initial P w) (List.replicate (32*(w.length+1)) false)=_ at he
  rw [he] at hm
  have hc:=matches_core hm rfl
  obtain ⟨i,o,hc⟩:=hc
  refine ⟨i,o,?_⟩
  have hb' : 2*(32*(w.length+1))=polynomialBudget 64 1 w.length := by
    simp [polynomialBudget];omega
  rw [hb'] at hc
  simpa only [boot_word,w,boot,P,machine,frame,wordState] using hc

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

 theorem pow_bits (b : ℕ) : (2^b).bits=List.replicate b false++[true] := by
  induction b with
  | zero=>rfl
  | succ b ih=>
    rw [pow_succ,show 2^b*2=Nat.bit false (2^b) from by simp [Nat.bit_val,Nat.mul_comm]]
    rw [Nat.bits_append_bit _ _ (fun hn=>False.elim ((pow_ne_zero b (by decide : (2:ℕ)≠0)) hn)),ih]
    simp only [List.replicate_succ,List.cons_append]

 theorem encodedNat (u : ℕ) : (trNat u).map FlatTM2.letters=u.bits.map digit := by
  rw [RawBits.trNat_bits,List.map_map]
  rfl
 theorem encodedList (u : ℕ) (xs : List ℕ) :
    (trList (u::xs)).map FlatTM2.letters=u.bits.map digit++sep::(trList xs).map FlatTM2.letters := by
  simp only [trList,List.map_append,List.map_cons,encodedNat]

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_WrapperStartup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}

 theorem construct_input (c : Turing.ToPartrec.Code) (v : List ℕ) (i : BitTape) :
    constructState (qa:=qa) (LiteralPartrec.input c v) i=
      wordState (.construct (LiteralPartrec.processor c).start) i ((trList v).map FlatTM2.letters) [] [] [] true := by
  have h:=LiteralInput.input_config c v
  have hc:=congrArg (fun s=>s.1) h
  have hs:=congrArg (fun s=>s.2.1) h
  have hy:=congrArg (fun s=>s.2.2) h
  change (LiteralPartrec.input c v).control=(LiteralPartrec.processor c).start at hc
  change (LiteralPartrec.input c v).yielded=false at hy
  apply wordState_ext
  · simp only [constructState,inside,hy,Bool.cond_false,hc,wordState]
  · rfl
  · intro k
    cases k with
    | base k=>
      change (LiteralPartrec.input c v).store (FlatTM2.keys k)=_
      have hh:=congrFun hs (FlatTM2.keys k)
      change (LiteralPartrec.input c v).store (FlatTM2.keys k)=
        (if FlatTM2.keys k=FlatTM2.keys K'.main then (trList v).map FlatTM2.letters else []) at hh
      rw [hh]
      cases k <;> simp [wordState]
    | pay=>rfl
    | buf=>rfl
  · rfl
  · rfl

 theorem construct_output {c : Turing.ToPartrec.Code} {v w : List ℕ}
    {t : ℕ} (hy : (StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
      (List.replicate t false)).yielded=true)
    (hs : ∀i,(StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
      (List.replicate t false)).store i=((halt w).stk (FlatTM2.keys.symm i)).map FlatTM2.letters)
    (i : BitTape) :
    constructState (qa:=qa) (StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
      (List.replicate t false)) i=wordState .pad i ((trList w).map FlatTM2.letters) [] [] [] true := by
  apply wordState_ext
  · simp only [constructState,inside,hy,Bool.cond_true,wordState]
  · rfl
  · intro k;cases k with
    | base k=>
      simp only [constructState,inside,hs,Equiv.symm_apply_apply,halt,wordState]
      cases k <;> rfl
    | pay=>rfl
    | buf=>rfl
  · rfl
  · rfl

 theorem literal_first {c : Turing.ToPartrec.Code} {v w : List ℕ}
    (h : w∈Turing.ToPartrec.Code.eval c v) :
    ∃t,(StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
      (List.replicate t false)).yielded=true ∧
      (∀j<t,(StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
        (List.replicate j false)).yielded=false) ∧
      ∀i,(StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
        (List.replicate t false)).store i=((halt w).stk (FlatTM2.keys.symm i)).map FlatTM2.letters := by
  obtain ⟨T,hT,hS⟩:=LiteralPartrec.halts h
  have he : ∃t,(StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
      (List.replicate t false)).yielded=true:=⟨T,hT⟩
  have ht:=Nat.find_spec he
  refine ⟨Nat.find he,ht,?_,?_⟩
  · intro j hj
    have hn:=Nat.find_min he hj
    cases hh:(StackCompiler.run (LiteralPartrec.processor c) (LiteralPartrec.input c v)
      (List.replicate j false)).yielded <;> simp_all
  · rw [←StackCompiler.capped_after _ _ ht (Nat.find_min' he hT)]
    exact hS

 theorem literal_prefix {c : Turing.ToPartrec.Code} {v w : List ℕ}
    (h : w∈Turing.ToPartrec.Code.eval c v)
    (A : StackCompiler.Processor qa (Fintype.card K') g) :
    ∃t,Nonempty (Prefix (processor (LiteralPartrec.processor c) A)
      (wordState (.construct (LiteralPartrec.processor c).start) BitTape.blank ((trList v).map FlatTM2.letters) [] [] [] true)
      (wordState .pad BitTape.blank ((trList w).map FlatTM2.letters) [] [] [] true) t) := by
  obtain ⟨t,ht,hp,hs⟩:=literal_first h
  have hh:=constructor_prefix (LiteralPartrec.processor c) A (StackPrimitive.literal_deterministic c)
    (LiteralPartrec.input c v) t hp
  rw [construct_input,construct_output ht hs] at hh
  exact ⟨t,⟨hh⟩⟩

 theorem startup_exists (mult a : ℕ) (v : ConstructorSearch.Cert)
    (h : v∈ConstructorSearch.search mult (ConstructorProgram.read a)) :
    ∃d,2^v.2.2≤d ∧ Nonempty (Prefix (uniform mult)
      (wordState (.construct (literalC mult).start) BitTape.blank ((trList [a]).map FlatTM2.letters) [] [] [] true)
      (ready (RuntimeCertificate.B (ConstructorProgram.read a).2.1 v.1)
        (Encodable.encode (RawProgram.initial (ConstructorProgram.read a).1 (ConstructorProgram.read a).2.1 v.1))
        BitTape.blank [] true) d) := by
  obtain ⟨t,⟨hp⟩⟩:=literal_prefix (ConstructorProgram.code_correct h) literalA
  let b:=RuntimeCertificate.B (ConstructorProgram.read a).2.1 v.1
  let u:=Encodable.encode (RawProgram.initial (ConstructorProgram.read a).1 (ConstructorProgram.read a).2.1 v.1)
  change Prefix (uniform mult) _
    (wordState .pad BitTape.blank ((trList [2^(2^v.2.2),2^b,u]).map FlatTM2.letters) [] [] [] true) t at hp
  rw [encodedList (2^(2^v.2.2))] at hp
  have hq:=padding_prefix (literalC mult) literalA (2^(2^v.2.2)).bits
    ((trList [2^b,u]).map FlatTM2.letters)
  have hh:=hp.append hq
  refine ⟨t+((2^(2^v.2.2):ℕ).bits.length+1),?_,⟨hh⟩⟩
  rw [pow_bits,List.length_append,List.length_replicate,List.length_singleton]
  omega

end UniformKServer.UniformWrapper

end

end OAI
end

section
-- module Solutions.Q220_UK.UniformKServer_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniformKServer
open UniformWrapper TypedStack
open scoped Classical

/-- The literal finite-control wrapper is a single horizon-free online machine.
The very large verified constructor is paid only through a finite, instance-
dependent initial delay; each request still takes the fixed linear bit budget. -/
theorem uniform_squared_logarithmic_main_oai : UniformAlgorithmClaim := by
  let mult : ℕ := ⌈PartitionTree.absoluteRate⌉₊
  have hm : PartitionTree.absoluteRate≤(mult:ℝ) := Nat.le_ceil _
  refine ⟨machine mult,64,1,OffsetInstance.coefficient mult,by norm_num,
    OffsetInstance.coefficient_positive mult,?_⟩
  intro n k hn hk hkn d s
  let : NeZero k := ⟨by omega⟩
  have hk0 : 0<k:=by omega
  have hkle : k≤n:=by omega
  let draw := (RawBinary.distances d).map RawMetric.present
  have hdr : ∀x y : Fin n,RawArithmetic.value (RawTable.dist n draw x.val y.val)=d.distance x y :=
    RawBinary.metric_input d
  have hx:=ConstructorSearch.exists_certificate (by omega : 2≤n) hk hkle mult hm d draw hdr
  have hdom:=ConstructorSearch.terminates hx
  let v:=(ConstructorSearch.search mult (n,k,draw)).get hdom
  have hvs : v∈ConstructorSearch.search mult (n,k,draw):=Part.get_mem hdom
  have hv:=ConstructorSearch.correct hvs
  simp only [ConstructorSearch.verify,Bool.and_eq_true_iff] at hv
  have hp:=RawAccepted.spec d draw hdr hv.1
  let a:=RawBinary.value (instanceCode d s++[true])
  have hi : ConstructorProgram.read a=(n,k,draw):=ConstructorProgram.read_code d s
  have hs : v∈ConstructorSearch.search mult (ConstructorProgram.read a) := by rw [hi];exact hvs
  obtain ⟨delay,hd,⟨p⟩⟩:=startup_exists mult a v hs
  simp only [hi] at p
  have hb:=boot_core mult d s
  have hz : CoreRep (uniform mult) (p.state 0) (boot (machine mult) 64 1 d s) := by
    rw [p.start]
    exact hb
  refine ⟨hb.yielded,?_,?_⟩
  · intro t z hreach r coins
    have hl:=all_reachable mult hk0 hkle v.1 hp.numbers.restart_pos hp.rows v.2 hv.2 delay hd _ p d s hb t z hreach
    exact (live_next mult (instanceCode d s).length hk0 hkle v.1 hp.numbers.restart_pos hp.rows
      v.2 hv.2 delay hd _ p t z hl r coins).2
  · obtain ⟨B,hB,hcost⟩:=RawControllerCost.delayed_bound hk hkle hm d draw hdr v.1 hv.1 s delay
    refine ⟨B,hB,?_⟩
    intro w
    have he:=prefix_expected mult (instanceCode d s).length hkle v.1 hp.numbers.restart_pos hp.rows
      v.2 hv.2 delay hd _ p d w 0 (Nat.zero_le _) (boot (machine mult) 64 1 d s) hz s
    have he' : machineExpectedCost (machine mult) 64 1 (instanceCode d s).length d hk0
        0 (boot (machine mult) 64 1 d s) s w=
        RawControllerCost.delayed hkle d draw hdr v.1 hv.1 s delay w := by
      simpa only [Nat.sub_zero,RawControllerCost.delayed,RawControllerCost.expected,RawControllerCost.N,
        RawControllerCost.u,tcExpected,tcInitial,tcRows,tcN] using he
    exact he'.trans_le (hcost w)

end UniformKServer

end

end OAI
end

theorem solution : type_of% @OAI.UniformKServer.uniform_squared_logarithmic_main_oai := @OAI.UniformKServer.uniform_squared_logarithmic_main_oai
