-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.op_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:47:36.655126+00:00
-- url     : https://prove2.me/submissions/35187132-cf6e-44f4-bf53-b19c6bb0ff4c

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L026
import Definitions.Def_Q238L028
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBlueBlocks_at_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFinSet_diff_pack_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MulComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRational

lemma decode_encode (x : ℚ) : decode (encode x)=x := by
  simp only [decode,numerator,denominator,encode,pairBits,extractPrefix_pair,discardPrefix_pair,
    Signed.encode_decode,value_bits,Rat.mkRat_self]

end BinaryRational
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations UnaryTake

namespace WordList

lemma cons_ne_nil (w ws : List Bool) : cons w ws≠[] := List.cons_ne_nil _ _

namespace ReverseMap

lemma next_nil (f : List Bool → List Bool) (d o : List Bool) :
    next f (pack true [] d o)=pack false [] d o := by
  simp only [next,While.next,head_pack,ite_true, if_true,step,counter_pack,data_pack,output_pack]
lemma next_cons (f : List Bool → List Bool) (w ws d o : List Bool) :
    next f (pack true (cons w ws) d o)=pack true ws d (cons (f (pairBits (d,w))) o) := by
  simp only [next,While.next,head_pack,ite_true, if_true,step,counter_pack,cons_ne_nil,ite_false, if_false,
    data_pack,output_pack,tail_cons,head_cons]
lemma loop_exact (f : List Bool → List Bool) (ws : List (List Bool)) (d : List Bool) (os : List (List Bool)) :
    (next f)^[ws.length+1] (pack true (encode ws) d (encode os))=
      pack false [] d (encode ((ws.map (fun w=>f (pairBits (d,w)))).reverse++os)) := by
  induction ws generalizing os with
  | nil => simp only [encode,List.length_nil,Nat.zero_add,Function.iterate_one,next_nil,
      List.map_nil,List.reverse_nil,List.nil_append]
  | cons w ws ih =>
    rw [List.length_cons,Function.iterate_succ_apply,encode,next_cons]
    change (next f)^[ws.length+1] (pack true (encode ws) d (encode (f (pairBits (d,w))::os)))=_
    rw [ih]
    simp only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append]
lemma loop_spec (f : List Bool → List Bool) (ws : List (List Bool)) (d : List Bool) :
    (next f)^[(encode ws).length+1] (pack true (encode ws) d [])=
      pack false [] d (encode ((ws.map (fun w=>f (pairBits (d,w)))).reverse)) := by
  have hl := length_le_encode ws
  have hlen : (encode ws).length+1=((encode ws).length-ws.length)+(ws.length+1) := by omega
  rw [hlen,Function.iterate_add_apply]
  change (next f)^[_] ((next f)^[ws.length+1] (pack true (encode ws) d (encode [])))=_
  rw [loop_exact,List.append_nil]
  apply While.next_fixed
  exact (by decide : (some false:Option Bool)≠some true)

lemma run_encode (f : List Bool → List Bool) (d : List Bool) (ws : List (List Bool)) :
    run f (pairBits (d,encode ws))=encode ((ws.map (fun w=>f (pairBits (d,w)))).reverse) := by
  simp only [run,extractPrefix_pairBits,discardPrefix_pairBits,rank,head_pack,ite_true, if_true,counter_pack,
    loop_spec,output_pack]
end ReverseMap

lemma reverse_encode (ws : List (List Bool)) : reverse (encode ws)=encode ws.reverse := by
  simp only [reverse,ReverseMap.run_encode,discardPrefix_pairBits,List.map_id']
lemma mapWith_encode (f : List Bool → List Bool) (d : List Bool) (ws : List (List Bool)) :
    mapWith f (pairBits (d,encode ws))=encode (ws.map (fun w=>f (pairBits (d,w)))) := by
  simp only [mapWith,Function.comp_apply,ReverseMap.run_encode,reverse_encode,List.reverse_reverse]

end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Step2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations
namespace WordList
lemma length_encode_append (xs ys : List (List Bool)) :
    (encode (xs++ys)).length=(encode xs).length+(encode ys).length := by
  induction xs with
  | nil => simp only [List.nil_append,encode,List.length_nil,Nat.zero_add]
  | cons x xs ih => simp only [List.cons_append,encode,length_cons,ih]; omega
lemma length_encode_drop (xs : List (List Bool)) (n : ℕ) :
    (encode (xs.drop n)).length ≤ (encode xs).length := by
  have h := length_encode_append (xs.take n) (xs.drop n)
  rw [List.take_append_drop] at h
  omega
namespace Fold

lemma length_pack (ws ctx a : List Bool) : (pack ws ctx a).length=2*ws.length+2*ctx.length+a.length+2 := by
  simp only [pack,pairBits_length]; omega
lemma step_nil (f : List Bool → List Bool) (ctx a : List Bool) :
    step f (pack (encode []) ctx a)=pack (encode []) ctx a := by
  simp only [step,items_pack,encode,ite_true, if_true]
lemma step_cons (f : List Bool → List Bool) (ctx a w : List Bool) (ws : List (List Bool)) :
    step f (pack (encode (w::ws)) ctx a)=pack (encode ws) ctx (operation f ctx a w) := by
  simp only [step,items_pack,encode,cons_ne_nil,ite_false, if_false,context_pack,head_cons,tail_cons,accum_pack,operation]
lemma iterate_pack (f : List Bool → List Bool) (ctx a : List Bool) (ws : List (List Bool)) (n : ℕ) :
    (step f)^[n] (pack (encode ws) ctx a)=
      pack (encode (ws.drop n)) ctx ((ws.take n).foldl (operation f ctx) a) := by
  induction n generalizing ws a with
  | zero => simp only [Function.iterate_zero_apply,List.drop_zero,List.take_zero,List.foldl_nil]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases ws with
    | nil =>
      rw [step_nil,Function.iterate_fixed (step_nil f ctx a)]
      rfl
    | cons w ws =>
      rw [step_cons,ih]
      simp only [List.drop_succ_cons,List.take_succ_cons,List.foldl_cons]

lemma run_encode (f : List Bool → List Bool) (R : Polynomial ℕ) (ctx a : List Bool)
    (ws : List (List Bool)) (B : ℕ)
    (hB : ∀ n,((ws.take n).foldl (operation f ctx) a).length ≤ B)
    (hR : 2*(encode ws).length+2*ctx.length+B+2 ≤ R.eval (pack (encode ws) ctx a).length) :
    run f R (pack (encode ws) ctx a)=ws.foldl (operation f ctx) a := by
  have he := BoundedIteration.polynomialRun_eq (step f) Polynomial.X R (pack (encode ws) ctx a) (by
    intro j _
    rw [iterate_pack,length_pack]
    have hd := length_encode_drop ws j
    have hb := hB j
    omega)
  simp only [run,Function.comp_apply,he,Polynomial.eval_X,iterate_pack,accum_pack]
  rw [List.take_of_length_le]
  have hw := length_le_encode ws
  rw [length_pack]
  omega
end Fold
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
attribute [local irreducible] WordList.mapWith WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run IntegerArray.sumWords 
open WordOperations BinaryArithmetic
namespace WordList
lemma length_member_le_encode {ws : List (List Bool)} {w : List Bool} (hw : w∈ws) :
    w.length≤(encode ws).length := by
  induction ws with
  | nil => simp only [List.not_mem_nil] at hw
  | cons v vs ih =>
    simp only [List.mem_cons] at hw
    rw [encode,length_cons]
    rcases hw with rfl|hv
    · omega
    · have hh := ih hv
      omega
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_OptionEncode
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations
namespace WordList.Find

lemma operation_pack (p : List Bool → Bool) (ctx a w : List Bool) :
    Fold.operation (operation p) ctx a w=
      if a=[] then if p (pairBits (ctx,w)) then true::w else [] else a := by
  simp only [Fold.operation,operation,accum,item,context,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits]
lemma fold_result (p : List Bool → Bool) (ctx a : List Bool) (ws : List (List Bool)) :
    ws.foldl (Fold.operation (operation p) ctx) a=
      if a=[] then optionEncode (ws.find? (fun w=>p (pairBits (ctx,w)))) else a := by
  induction ws generalizing a with
  | nil => simp only [List.foldl_nil,List.find?_nil,optionEncode]; split_ifs with h <;> simp_all
  | cons w ws ih =>
    rw [List.foldl_cons,operation_pack,ih]
    by_cases ha : a=[]
    · subst a
      simp only [ite_true, if_true]
      cases hp : p (pairBits (ctx,w)) <;> simp [hp,optionEncode]
    · simp only [ha,ite_false, if_false]

lemma optionEncode_bound {ws : List (List Bool)} {p : List Bool → Bool} :
    (optionEncode (ws.find? p)).length≤(encode ws).length+1 := by
  cases h : ws.find? p with
  | none => simp only [optionEncode,List.length_nil]; omega
  | some w =>
    have hw : w∈ws := List.mem_of_find?_eq_some h
    have hh := length_member_le_encode hw
    simpa only [optionEncode,List.length_cons] using Nat.add_le_add_right hh 1
lemma run_encode (p : List Bool → Bool) (ctx : List Bool) (ws : List (List Bool)) :
    run p (pairBits (ctx,encode ws))=optionEncode (ws.find? (fun w=>p (pairBits (ctx,w)))) := by
  unfold run
  simp only [Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [Fold.run_encode (operation p) (3*Polynomial.X+3) ctx [] ws ((encode ws).length+1)]
  · simp only [fold_result,ite_true, if_true]
  · intro j
    rw [fold_result,ite_eq_left rfl]
    have hb : (optionEncode ((ws.take j).find? (fun w=>p (pairBits (ctx,w))))).length≤
        (encode (ws.take j)).length+1 := optionEncode_bound
    have he := length_encode_append (ws.take j) (ws.drop j)
    rw [List.take_append_drop] at he
    omega
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_X,Fold.length_pack,List.length_nil]
    omega
end WordList.Find
end
open WordOperations BinaryArithmetic RationalLinearFeasibility
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundedDecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations
namespace WordList
namespace Count
lemma operation_eq (ctx a w : List Bool) : Fold.operation op ctx a w=true::a := by
  simp only [Fold.operation,op,Function.comp_apply,Fold.accum,discardPrefix_pairBits]
lemma fold_op (ws : List (List Bool)) (a : List Bool) (ctx : List Bool) :
    ws.foldl (Fold.operation op ctx) a=List.replicate ws.length true++a := by
  induction ws generalizing a with
  | nil => simp only [List.foldl_nil,List.length_nil,List.replicate_zero,List.nil_append]
  | cons w ws ih =>
    simp only [List.foldl_cons,operation_eq,ih,List.length_cons]
    rw [←List.singleton_append,←List.append_assoc,←List.replicate_succ',List.replicate_succ]
lemma run_encode (ws : List (List Bool)) : run (encode ws)=List.replicate ws.length true := by
  unfold run
  rw [Fold.run_encode op (4*Polynomial.X+4) [] [] ws (encode ws).length]
  · simp only [fold_op,List.append_nil]
  · intro n
    simp only [fold_op,List.append_nil,List.length_replicate]
    have ht : (ws.take n).length ≤ ws.length := by simp only [List.length_take]; omega
    exact ht.trans (length_le_encode ws)
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
end Count
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CappedFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.CappedFold
open WordOperations
lemma run_pack (f : List Bool → List Bool) (cap ctx a : List Bool) (ws : List (List Bool))
    (hB : ∀ n, ((ws.take n).foldl (Fold.operation f ctx) a).length ≤ cap.length) :
    run f (pairBits (cap,Fold.pack (encode ws) ctx a))=ws.foldl (Fold.operation f ctx) a := by
  unfold run
  rw [discardPrefix_pairBits,Fold.items_pack,Count.run_encode,BoundedIteration.run_eq]
  · simp only [List.length_replicate,Fold.iterate_pack,Fold.accum_pack,List.take_length]
  · intro j _
    rw [Fold.iterate_pack,Fold.length_pack,RepeatedAppend.length_copies,pairBits_length,Fold.length_pack]
    dsimp only at *
    have hws:=length_encode_drop ws j
    have hb:=hB j
    omega

lemma fold_encode {S A : Type*} (encS : S → List Bool) (encA : A → List Bool)
    (g : S → A → S) (f : List Bool → List Bool) (ctx : List Bool)
    (hf : ∀ s a,f (pairBits (ctx,pairBits (encA a,encS s)))=encS (g s a))
    (s : S) (xs : List A) :
    (xs.map encA).foldl (Fold.operation f ctx) (encS s)=encS (xs.foldl g s) := by
  induction xs generalizing s with
  | nil=>rfl
  | cons a xs ih=>
    simp only [List.map_cons,List.foldl_cons,Fold.operation,hf]
    exact ih (g s a)
lemma run_typed {S A : Type*} (encS : S → List Bool) (encA : A → List Bool)
    (g : S → A → S) (f : List Bool → List Bool) (ctx cap : List Bool)
    (hf : ∀ s a,f (pairBits (ctx,pairBits (encA a,encS s)))=encS (g s a))
    (s : S) (xs : List A) (hB : ∀ n,(encS ((xs.take n).foldl g s)).length ≤ cap.length) :
    run f (pairBits (cap,Fold.pack (encode (xs.map encA)) ctx (encS s)))=encS (xs.foldl g s) := by
  rw [run_pack]
  · exact fold_encode encS encA g f ctx hf s xs
  · intro n
    rw [←List.map_take,fold_encode encS encA g f ctx hf]
    exact hB n
end MetricKMedianRecovery.BitMachine.WordList.CappedFold

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueChoice
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueChoice
open WordOperations WordList BinaryArithmetic
variable {A : Type*}
lemma run_pack (enc : A→List Bool) (x y : BlueDP.Candidate A) :
    run (pairBits (encode enc x,encode enc y))=encode enc (BlueDP.choose x y) := by
  rw [run,extractPrefix_pairBits,discardPrefix_pairBits]
  cases x with
  | none=>rw [show encode enc none=[] from rfl,ite_eq_left rfl];rfl
  | some x=>
    cases x with
    | mk q a=>
      have hx : encode enc (some (q,a))≠[] := by simp [encode,WordList.encode,WordList.cons,pairBits]
      rw [ite_eq_right hx]
      cases y with
      | none=>rw [show encode enc none=[] from rfl,ite_eq_left rfl];rfl
      | some y=>
        cases y with
        | mk r b=>
          have hy : encode enc (some (r,b))≠[] := by simp [encode,WordList.encode,WordList.cons,pairBits]
          rw [ite_eq_right hy]
          simp only [score,encode,WordList.encode,head_cons,extractPrefix_pairBits,BinaryRational.decode_encode,BlueDP.choose]
          split_ifs <;> rfl

lemma select_pack (enc : A→List Bool) (xs : List (BlueDP.Candidate A)) :
    select (WordList.encode (xs.map (encode enc)))=encode enc (BlueDP.select xs) := by
  rw [select]
  change CappedFold.run step (pairBits (WordList.encode (xs.map (encode enc)),
    Fold.pack (WordList.encode (xs.map (encode enc))) [] (encode enc none)))=_
  apply CappedFold.run_typed (encode enc) (encode enc) BlueDP.choose step [] _ (s:=none) (xs:=xs)
  · intro s a
    simp only [step,Fold.accum,Find.item,Function.comp_apply,discardPrefix_pairBits,extractPrefix_pairBits,run_pack]
  · intro n
    rcases BlueDP.fold_mem (xs.take n) (none : BlueDP.Candidate A) with he|he
    · rw [he];simp [encode]
    · exact length_member_le_encode (List.mem_map.mpr ⟨_,List.mem_of_mem_take he,rfl⟩)

end MetricKMedianRecovery.BitMachine.BinaryBlueChoice

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueMerge
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueMerge
open WordOperations WordList
variable {A : Type*}
lemma listEnc_append (enc : A→List Bool) (xs ys : List A) : listEnc enc (xs++ys)=listEnc enc xs++listEnc enc ys := by
  simp only [listEnc,List.map_append,WordList.encode_append]
lemma run_pack (enc : A→List Bool) (x y : BlueDP.Candidate (List A)) :
    run (pairBits (BinaryBlueChoice.encode (listEnc enc) x,BinaryBlueChoice.encode (listEnc enc) y))=
      BinaryBlueChoice.encode (listEnc enc) (BlueDP.merge x y) := by
  cases x with
  | none=>simp [run,BinaryBlueChoice.encode,BlueDP.merge]
  | some x=>
    cases x with
    | mk q xs=>
      cases y with
      | none=>simp [run,BinaryBlueChoice.encode,BlueDP.merge]
      | some y=>
        cases y with
        | mk r ys=>
          simp only [run,extractPrefix_pairBits,discardPrefix_pairBits]
          have hx : BinaryBlueChoice.encode (listEnc enc) (some (q,xs))≠[] := by
            simp [BinaryBlueChoice.encode,WordList.encode,WordList.cons,pairBits]
          have hy : BinaryBlueChoice.encode (listEnc enc) (some (r,ys))≠[] := by
            simp [BinaryBlueChoice.encode,WordList.encode,WordList.cons,pairBits]
          rw [ite_eq_right hx,ite_eq_right hy]
          simp only [output,sum,extractPrefix_pairBits,discardPrefix_pairBits,BinaryBlueChoice.encode,
            WordList.encode,head_cons,extractPrefix_pairBits,BinaryBlueChoice.score,payload,
            discardPrefix_pairBits,BinaryRational.decode_encode,BlueDP.merge,listEnc_append]
end MetricKMedianRecovery.BitMachine.BinaryBlueMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordEq
lemma eq_pair (xs ys : List Bool) : eq (pairBits (xs,ys))=decide (xs=ys) := by
  simp only [eq,extractPrefix_pairBits,discardPrefix_pairBits]
end WordEq
namespace WordList
lemma encode_injective : Function.Injective encode := by
  intro xs
  induction xs with
  | nil=>
    intro ys he
    cases ys with
    | nil=>rfl
    | cons y ys=>exact (cons_ne_nil y (encode ys) he.symm).elim
  | cons x xs ih=>
    intro ys he
    cases ys with
    | nil=>exact (cons_ne_nil x (encode xs) he).elim
    | cons y ys=>
      have hh:=congrArg head he
      have ht:=congrArg tail he
      simp only [encode,head_cons] at hh
      simp only [encode,tail_cons] at ht
      exact congrArg₂ List.cons hh (ih ht)
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
variable {n : ℕ}
lemma values_sort (S : Finset (Fin n)) : (values S).sort (·≤·)=(S.sort (·≤·)).map Fin.val := by
  let f : Fin n ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩
  have hh := Finset.map_sort f S (·≤·) (·≤·) (fun a _ b _=>show a≤b↔a.val≤b.val from Iff.rfl)
  simpa only [f,Finset.map_eq_image,values,Function.Embedding.coeFn_mk] using hh.symm
lemma encode_eq (S : Finset (Fin n)) : encode S=WordList.encode ((S.sort (·≤·)).map (fun i=>i.val.bits)) := by
  rw [encode,BinaryNatSet.encode,BinaryNatSet.pack,values_sort,List.map_map]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryFinSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueItem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueChoice
lemma select_map {A R : Type*} (enc : A→List Bool) (f : R→BlueDP.Candidate A) (rs : List R) :
    select (WordList.encode (rs.map (fun r=>encode enc (f r))))=encode enc (BlueDP.select (rs.map f)) := by
  simpa only [List.map_map,Function.comp_def] using select_pack enc (rs.map f)
end MetricKMedianRecovery.BitMachine.BinaryBlueChoice

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueBlocksMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueBlocks
open WordOperations WordList
variable {L R : Type*} [LinearOrder L] [LinearOrder R] {n : ℕ}
lemma run_pack (el : L→List Bool) (er : R→List Bool) (hel : Function.Injective el) (B : Finset R) (F : Finset (Fin n))
    (label : R→L) (q : R→Fin n→ℚ) (U : Finset L) :
    run (pairBits (pairBits (BinaryBlueItem.records el er B label q,labelsEnc el U),BinaryFinSet.encode F))=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueItem.atomEnc el er)) (BlueDP.block B F label q U) := by
  simp only [run,BinaryFinSet.encode_eq,mapWith_encode,List.map_map,Function.comp_def,atCall,extractPrefix_pairBits,
    discardPrefix_pairBits,at_pack_s238r el er hel]
  rw [BinaryBlueChoice.select_map]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryBlueBlocks

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueLookup
open WordOperations WordList
variable {L A : Type*} [LinearOrder L]
lemma run_pack (key : Finset L→List Bool) (enc : A→List Bool) (hk : Function.Injective key)
    (T : BlueDP.Table L A) (U : Finset L) : run (pairBits (key U,encode key enc T))=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc enc) (BlueDP.lookup U T) := by
  simp only [run,encode,Find.run_encode]
  induction T with
  | nil=>simp [Find.optionEncode,BlueDP.lookup,BinaryBlueChoice.encode,List.tail,discardPrefix]
  | cons z T ih=>
    rcases z with ⟨V,c⟩
    simp only [List.map_cons,List.find?_cons,matchKey,extractPrefix_pairBits,discardPrefix_pairBits,WordEq.eq_pair,
      hk.eq_iff,BlueDP.lookup]
    split_ifs with h
    · simp [h,Find.optionEncode,List.tail]
    · simp only [h,decide_false]
      simpa only [matchKey,extractPrefix_pairBits,discardPrefix_pairBits,WordEq.eq_pair] using ih
end MetricKMedianRecovery.BitMachine.BinaryBlueLookup
namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
lemma encode_injective {n : ℕ} : Function.Injective (@encode n) := by
  intro S T he
  rw [encode_eq,encode_eq] at he
  have hh:=WordList.encode_injective he
  have hin : Function.Injective (fun i : Fin n=>i.val.bits) := by
    intro i j hij
    apply Fin.val_injective
    have h:=congrArg BinaryArithmetic.value hij
    simpa only [BinaryArithmetic.value_bits] using h
  have hh' := List.map_injective_iff.mpr hin hh
  simpa only [Finset.sort_toFinset] using congrArg List.toFinset hh'
end MetricKMedianRecovery.BitMachine.BinaryFinSet

namespace MetricKMedianRecovery.BitMachine.BinaryBlueCell
open WordOperations WordList
open BinaryOpeningPayment (field field_encode)
variable {n m : ℕ} {R : Type*} [LinearOrder R]
lemma finValBits_injective : Function.Injective (fun i : Fin m=>i.val.bits) := by
  intro i j h
  have hh:=congrArg BinaryArithmetic.value h
  exact Fin.val_injective (by simpa only [BinaryArithmetic.value_bits] using hh)
lemma op_pack_s238r_oai (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U W V : Finset (Fin m)) (T : BlueDP.Table (Fin m) (BlueDP.Atom (Fin m) R (Fin n))) :
    op (pairBits (pairBits (ctxPack er B F label q U T,BinaryFinSet.encode W),BinaryFinSet.encode V))=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (atomEnc er))
        (BlueDP.merge (BlueDP.block B F label q V) (BlueDP.lookup (W\V) T)) := by
  simp only [op,block,old,ctx,whole,extractPrefix_pairBits,discardPrefix_pairBits,ctxPack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFinSet.diff_pack_s238r]
  rw [show BinaryFinSet.encode V=BinaryBlueBlocks.labelsEnc (fun i : Fin m=>i.val.bits) V by
    exact BinaryFinSet.encode_eq V]
  rw [BinaryBlueBlocks.run_pack _ er finValBits_injective]
  rw [BinaryBlueLookup.run_pack _ _ BinaryFinSet.encode_injective,BinaryBlueMerge.run_pack]
end MetricKMedianRecovery.BitMachine.BinaryBlueCell

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.op_pack_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.op_pack_s238r_oai.{u_1}
