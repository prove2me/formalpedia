-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryBlueTable.next_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:42:21.926743+00:00
-- url     : https://prove2.me/submissions/c9fb6ebb-44a3-4a31-b344-62314a078222

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L026
import Definitions.Def_Q238L028
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBlueCell_op_pack_s238r

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
lemma length_encode_take (xs : List (List Bool)) (n : ℕ) :
    (encode (xs.take n)).length ≤ (encode xs).length := by
  have h := length_encode_append (xs.take n) (xs.drop n)
  rw [List.take_append_drop] at h
  omega
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Op2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations
namespace WordList
namespace Flatten

lemma operation_eq (ctx a w : List Bool) : Fold.operation op ctx a w=a++w := by
  simp only [Fold.operation,op,Fold.accum,Find.item,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits]
lemma fold_eq (ws : List (List Bool)) (ctx a : List Bool) :
    ws.foldl (Fold.operation op ctx) a=a++ws.flatten := by
  induction ws generalizing a with
  | nil=>simp only [List.foldl_nil,List.flatten_nil,List.append_nil]
  | cons w ws ih=>simp only [List.foldl_cons,operation_eq,ih,List.flatten_cons,List.append_assoc]
lemma length_flatten_le (ws : List (List Bool)) : ws.flatten.length≤(encode ws).length := by
  induction ws with
  | nil=>rfl
  | cons w ws ih=>simp only [List.flatten_cons,List.length_append,encode,length_cons]; omega
lemma run_encode (ws : List (List Bool)) : run (encode ws)=ws.flatten := by
  unfold run
  rw [Fold.run_encode op (3*Polynomial.X+3) [] [] ws (encode ws).length]
  · simp only [fold_eq,List.nil_append]
  · intro n
    simp only [fold_eq,List.nil_append]
    exact (length_flatten_le _).trans (length_encode_take ws n)
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
lemma encode_flatMap {α : Type*} (ws : List α) (f : α → List (List Bool)) :
    encode (ws.flatMap f)=(ws.map (fun x=>encode (f x))).flatten := by
  induction ws with
  | nil=>rfl
  | cons a ws ih=>simp only [List.flatMap_cons,encode_append,List.map_cons,List.flatten_cons,ih]
end Flatten
lemma flatMapWith_encode (f : List Bool → List Bool) (ctx : List Bool) (ws : List (List Bool))
    (g : List Bool → List (List Bool)) (h : ∀ w∈ws, f (pairBits (ctx,w))=encode (g w)) :
    flatMapWith f (pairBits (ctx,encode ws))=encode (ws.flatMap g) := by
  simp only [flatMapWith,Function.comp_apply,mapWith_encode,Flatten.run_encode,Flatten.encode_flatMap]
  congr 1
  apply List.map_congr_left
  exact h
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FilterItem
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
lemma filterWith_encode (p : List Bool → Bool) (ctx : List Bool) (ws : List (List Bool)) :
    filterWith p (pairBits (ctx,encode ws))=encode (ws.filter (fun w=>p (pairBits (ctx,w)))) := by
  unfold filterWith
  rw [flatMapWith_encode (filterItem p) ctx ws (fun w=>if p (pairBits (ctx,w)) then [w] else []) (by
    intro w _; simp only [filterItem,discardPrefix_pairBits]; split <;> rfl)]
  congr 1
  induction ws with
  | nil=>rfl
  | cons w ws ih=>cases h : p (pairBits (ctx,w)) <;> simp [h,ih]
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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordSubsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Subsets
open WordOperations
variable {A : Type*}
lemma fold_from (p xs : List A) : xs.foldl update p.sublists=(p++xs).sublists := by
  induction xs generalizing p with
  | nil=>simp
  | cons a xs ih=>
    rw [List.foldl_cons]
    change xs.foldl update (p.sublists++p.sublists.map (fun s=>s++[a]))=_
    rw [←List.sublists_concat,ih]
    simp only [List.append_assoc,List.singleton_append]
lemma fold_empty (xs : List A) : xs.foldl update [[]]=xs.sublists := by simpa using fold_from [] xs
lemma op_pack (ss : List (List (List Bool))) (a : List Bool) :
    op (pairBits ([],pairBits (a,encode (ss.map encode))))=encode ((update ss a).map encode) := by
  simp only [op,added,Fold.accum,Find.item,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    mapWith_encode,List.map_map,Function.comp_def,addLast,encode_append,update,List.map_append]
lemma length_encode_sublist (xs ys : List (List Bool)) (h : xs.Sublist ys) : (encode xs).length≤(encode ys).length := by
  induction h with
  | slnil=>rfl
  | @cons a xs ys h ih=>simp only [encode,length_cons];omega
  | @cons_cons a xs ys h ih=>simp only [encode,length_cons];omega
lemma encode_bound (ws : List (List Bool)) (B : ℕ) (h : ∀ w∈ws,w.length≤B) :
    (encode ws).length≤ws.length*(2*B+2) := by
  induction ws with
  | nil=>simp [encode]
  | cons w ws ih=>
    have hw:=h w (by simp)
    have ht:=ih (fun x hx=>h x (by simp [hx]))
    simp only [encode,length_cons,List.length_cons]
    nlinarith
lemma subset_bound (ws : List (List Bool)) :
    (encode (ws.sublists.map encode)).length≤2^ws.length*(2*(encode ws).length+2) := by
  have h:=encode_bound (ws.sublists.map encode) (encode ws).length (by
    intro w hw
    obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hw
    exact length_encode_sublist s ws (List.mem_sublists.mp hs))
  simpa only [List.length_map,List.length_sublists] using h
lemma prefix_bound (ws : List (List Bool)) (j : ℕ) :
    (encode ((ws.take j).sublists.map encode)).length≤2^ws.length*(2*(encode ws).length+2) := by
  apply (subset_bound (ws.take j)).trans
  apply Nat.mul_le_mul
  · exact Nat.pow_le_pow_right (by omega) (by simp only [List.length_take]; exact Nat.min_le_right ..)
  · have h:=length_encode_take ws j
    omega
lemma run_pack (d : ℕ) (ctx : List Bool) (ws : List (List Bool))
    (h : 2^ws.length*(2*(encode ws).length+2)≤((pairBits (ctx,encode ws)).length+1)^d) :
    run d (pairBits (ctx,encode ws))=encode (ws.sublists.map encode) := by
  unfold run
  rw [discardPrefix_pairBits]
  have hb (j : ℕ) : (encode (((ws.take j).foldl update [[]]).map encode)).length ≤ ((cap d).word (pairBits (ctx,encode ws))).length := by
    rw [fold_empty,(cap d).word_length]
    simp only [Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    exact (prefix_bound ws j).trans h
  have hh := CappedFold.run_typed (fun ss : List (List (List Bool))=>encode (ss.map encode)) id update op [] ((cap d).word (pairBits (ctx,encode ws))) op_pack [[]] ws hb
  simpa only [List.map_id,fold_empty,List.map_cons,List.map_nil,show encode ([] : List (List Bool))=[] from rfl] using hh
end MetricKMedianRecovery.BitMachine.WordList.Subsets

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueTable
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L A : Type*} [LinearOrder L]
lemma mem_states (U V : Finset L) : V∈states U ↔ V⊆U := by
  simp only [states,List.mem_map,List.mem_sublists]
  constructor
  · rintro ⟨xs,hxs,rfl⟩
    intro l hl
    exact (Finset.mem_sort (·≤·)).mp (hxs.subset (List.mem_toFinset.mp hl))
  · intro h
    refine ⟨(U.sort (·≤·)).filter (fun l=>l∈V),List.filter_sublist,?_⟩
    ext l
    simp only [List.mem_toFinset,List.mem_filter,Finset.mem_sort,decide_eq_true_eq]
    exact ⟨And.right,fun hv=>⟨h hv,hv⟩⟩
lemma states_length (U : Finset L) : (states U).length=2^U.card := by
  simp [states,List.length_sublists]
end MetricKMedianRecovery.BlueDP

namespace MetricKMedianRecovery.BitMachine.BinaryBlueStates
open WordOperations WordList
variable {n : ℕ}
lemma key_sublist (U : Finset (Fin n)) (xs : List (Fin n)) (h : xs.Sublist (U.sort (·≤·))) :
    BinaryFinSet.encode xs.toFinset=WordList.encode (xs.map (fun i=>i.val.bits)) := by
  rw [BinaryFinSet.encode_eq,(List.toFinset_sort (r:=(·≤·)) (List.Nodup.sublist h (Finset.sort_nodup U (·≤·)))).mpr
    (List.Pairwise.sublist h (Finset.pairwise_sort U (·≤·)))]
lemma states_encode (U : Finset (Fin n)) :
    WordList.encode ((BlueDP.states U).map BinaryFinSet.encode)=
      WordList.encode (((U.sort (·≤·)).map (fun i=>i.val.bits)).sublists.map WordList.encode) := by
  simp only [BlueDP.states,List.sublists_map,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro xs hx
  exact key_sublist U xs (List.mem_sublists.mp hx)
lemma run_pack (d : ℕ) (ctx : List Bool) (U : Finset (Fin n))
    (hb : 2^U.card*(2*(BinaryFinSet.encode U).length+2)≤((pairBits (ctx,BinaryFinSet.encode U)).length+1)^d) :
    run d (pairBits (ctx,BinaryFinSet.encode U))=WordList.encode ((BlueDP.states U).map BinaryFinSet.encode) := by
  rw [run,BinaryFinSet.encode_eq,Subsets.run_pack]
  · exact (states_encode U).symm
  · simpa only [List.length_map,Finset.length_sort,←BinaryFinSet.encode_eq] using hb
lemma key_empty (U : Finset (Fin n)) : BinaryFinSet.encode U=[] ↔ U=∅ := by
  constructor
  · intro he
    have hh:=WordList.length_le_encode ((U.sort (·≤·)).map (fun i=>i.val.bits))
    rw [←BinaryFinSet.encode_eq,he] at hh
    simp only [List.length_map,Finset.length_sort,List.length_nil] at hh
    exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hh)
  · rintro rfl
    simp [BinaryFinSet.encode_eq,WordList.encode]
lemma nonemptyKey_pair (U : Finset (Fin n)) :
    nonemptyKey (pairBits ([],BinaryFinSet.encode U))=decide (U≠∅) := by
  simp [nonemptyKey,key_empty]
lemma blocks_pack (d : ℕ) (ctx : List Bool) (U : Finset (Fin n))
    (hb : 2^U.card*(2*(BinaryFinSet.encode U).length+2)≤((pairBits (ctx,BinaryFinSet.encode U)).length+1)^d) :
    blocks d (pairBits (ctx,BinaryFinSet.encode U))=WordList.encode ((BlueDP.enumBlocks U).map BinaryFinSet.encode) := by
  rw [blocks,run_pack d ctx U hb,filterWith_encode]
  simp only [List.filter_map,Function.comp_def,nonemptyKey_pair,BlueDP.enumBlocks,BlueDP.states]
end MetricKMedianRecovery.BitMachine.BinaryBlueStates

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList
lemma member_length {ws : List (List Bool)} {w : List Bool} (hw : w∈ws) : w.length≤(encode ws).length := by
  induction ws with
  | nil=>exact False.elim (List.not_mem_nil hw)
  | cons v vs ih=>
    rw [encode,length_cons]
    rcases List.mem_cons.mp hw with rfl|hw
    · omega
    · have h:=ih hw
      omega
end MetricKMedianRecovery.BitMachine.WordList

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueCell
open WordOperations WordList
open BinaryOpeningPayment (field field_encode)
variable {n m : ℕ} {R : Type*} [LinearOrder R]
lemma subset_capacity (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U W : Finset (Fin m)) (T : BlueDP.Table (Fin m) (BlueDP.Atom (Fin m) R (Fin n))) (hW : W⊆U) :
    2^W.card*(2*(BinaryFinSet.encode W).length+2)≤
      ((pairBits (ctxPack er B F label q U T,BinaryFinSet.encode W)).length+1)^3 := by
  have hu : 2^U.card≤(ctxPack er B F label q U T).length := by
    apply (show 2^U.card≤(encode ((BlueDP.states U).map BinaryFinSet.encode)).length from by
      simpa only [List.length_map,BlueDP.states_length] using length_le_encode ((BlueDP.states U).map BinaryFinSet.encode)).trans
    exact member_length (by simp)
  have hw : 2^W.card≤(ctxPack er B F label q U T).length :=
    (Nat.pow_le_pow_right (by omega) (Finset.card_le_card hW)).trans hu
  simp only [pairBits_length]
  calc
    _ ≤ (ctxPack er B F label q U T).length*(2*(BinaryFinSet.encode W).length+2) := Nat.mul_le_mul_right _ hw
    _ ≤ (2*(ctxPack er B F label q U T).length+1+(BinaryFinSet.encode W).length+1)^2 := by nlinarith
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
lemma run_pack (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U W : Finset (Fin m)) (T : BlueDP.Table (Fin m) (BlueDP.Atom (Fin m) R (Fin n))) (hW : W⊆U) :
    run (pairBits (ctxPack er B F label q U T,BinaryFinSet.encode W))=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (atomEnc er))
        (BlueDP.select ((BlueDP.enumBlocks W).map (fun V=>BlueDP.merge (BlueDP.block B F label q V) (BlueDP.lookup (W\V) T)))) := by
  rw [run,BinaryBlueStates.blocks_pack 3 _ W (subset_capacity er B F label q U W T hW),mapWith_encode]
  simp only [List.map_map,Function.comp_def,op_pack_s238r]
  exact BinaryBlueChoice.select_map _ _ _
end MetricKMedianRecovery.BitMachine.BinaryBlueCell

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueNextTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueTable
open WordOperations WordList
open BinaryOpeningPayment (field field_encode)
variable {n m : ℕ} {R : Type*} [LinearOrder R]
lemma next_pack_s238r_oai (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (T : BlueDP.Table (Fin m) (BlueDP.Atom (Fin m) R (Fin n))) :
    next (BinaryBlueCell.ctxPack er B F label q U T)=
      BinaryBlueLookup.encode BinaryFinSet.encode (BinaryBlueCell.atomEnc er) (BlueDP.nextTable (BlueDP.block B F label q) U T) := by
  unfold next
  rw [show field 2 (BinaryBlueCell.ctxPack er B F label q U T)=encode ((BlueDP.states U).map BinaryFinSet.encode) by
    simp only [BinaryBlueCell.ctxPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]]
  simp only [mapWith_encode,List.map_map,Function.comp_def,BinaryBlueLookup.encode,BlueDP.nextTable]
  congr 1
  apply List.map_congr_left
  intro W hW
  simp only [row,discardPrefix_pairBits,BinaryBlueCell.run_pack er B F label q U W T ((BlueDP.mem_states U W).mp hW)]
end MetricKMedianRecovery.BitMachine.BinaryBlueTable

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryBlueTable.next_pack_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.BitMachine.BinaryBlueTable.next_pack_s238r_oai.{u_1}
