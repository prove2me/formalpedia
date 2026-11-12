-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.find_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:58:40.593548+00:00
-- url     : https://prove2.me/submissions/db2f1418-bafa-446b-92ad-11caf6294aad

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L026
import Definitions.Def_Q238L034

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
namespace Signed
lemma encode_length (z : ℤ) : (encode z).length=z.natAbs.size+1 := by
  simp only [encode,List.length_cons,Nat.size_eq_bits_len]
lemma natSize_add (a b : ℕ) : (a+b).size ≤ a.size+b.size+1 := by
  apply Nat.size_le.mpr
  have ha : a<2^(a.size+b.size) := (Nat.lt_size_self a).trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  have hb : b<2^(a.size+b.size) := (Nat.lt_size_self b).trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
  calc
    a+b < 2^(a.size+b.size)+2^(a.size+b.size) := Nat.add_lt_add ha hb
    _ = 2^(a.size+b.size+1) := by rw [pow_succ]; omega
lemma encode_add_length (a b : ℤ) :
    (encode (a+b)).length ≤ (encode a).length+(encode b).length := by
  simp only [encode_length]
  have h := (Nat.size_le_size (Int.natAbs_add_le a b)).trans (natSize_add a.natAbs b.natAbs)
  omega
lemma encode_sum_length (xs : List ℤ) :
    (encode xs.sum).length ≤ 1+((xs.map encode).map List.length).sum := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    simp only [List.sum_cons,List.map_cons]
    have h := encode_add_length x xs.sum
    omega
end Signed
namespace WordList
lemma length_encode_take (xs : List (List Bool)) (n : ℕ) :
    (encode (xs.take n)).length ≤ (encode xs).length := by
  have h := length_encode_append (xs.take n) (xs.drop n)
  rw [List.take_append_drop] at h
  omega
end WordList
namespace IntegerArray

lemma fold_add (xs : List ℤ) (a : ℤ) (ctx : List Bool) :
    (xs.map Signed.encode).foldl (WordList.Fold.operation addOp ctx) (Signed.encode a)=
      Signed.encode (a+xs.sum) := by
  induction xs generalizing a with
  | nil => simp only [List.map_nil,List.foldl_nil,List.sum_nil,add_zero]
  | cons x xs ih =>
    simp only [List.map_cons,List.foldl_cons,WordList.Fold.operation,addOp,
      extractPrefix_pairBits,discardPrefix_pairBits,Signed.encode_decode,ih,List.sum_cons]
    congr 1
    ring

lemma sumWords_encode (xs : List ℤ) : sumWords (encode xs)=Signed.encode xs.sum := by
  unfold sumWords encode
  rw [WordList.Fold.run_encode addOp (4*Polynomial.X+4) [] (Signed.encode 0)
    (xs.map Signed.encode) (1+(WordList.encode (xs.map Signed.encode)).length)]
  · simpa only [zero_add] using fold_add xs 0 []
  · intro n
    rw [←List.map_take,fold_add,zero_add]
    have hs := Signed.encode_sum_length (xs.take n)
    have hl := WordList.length_encode (xs.take n |>.map Signed.encode)
    have ht := WordList.length_encode_take (xs.map Signed.encode) n
    rw [←List.map_take] at ht
    omega
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      WordList.Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
end IntegerArray
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations
namespace WordList
lemma length_encode_reverse (xs : List (List Bool)) : (encode xs.reverse).length=(encode xs).length := by
  simp only [length_encode,List.map_reverse,List.sum_reverse,List.length_reverse]
end WordList
end
open WordOperations BinaryArithmetic
namespace WordList
lemma encode_le_bound (ws : List (List Bool)) (B : ℕ) (hB : ∀ w∈ws,w.length ≤ B) :
    (encode ws).length ≤ ws.length*(2*B+2) := by
  induction ws with
  | nil => simp only [encode,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons w ws ih =>
    have hw := hB w (List.mem_cons_self ..)
    have ht := ih (fun x hx=>hB x (List.mem_cons_of_mem _ hx))
    simp only [encode,length_cons,List.length_cons]
    nlinarith
namespace Indices

lemma op_pair (w : List Bool) (a : ℕ) (os : List (List Bool)) :
    Fold.operation op [] (pairBits (a.bits,encode os)) w=
      pairBits ((a+1).bits,encode (a.bits::os)) := by
  simp only [Fold.operation,op,discardPrefix_pairBits,extractPrefix_pairBits,value_bits,encode]
lemma fold_eq (ws os : List (List Bool)) (a : ℕ) :
    ws.foldl (Fold.operation op []) (pairBits (a.bits,encode os))=
      pairBits ((a+ws.length).bits,encode ((List.range' a ws.length |>.map Nat.bits).reverse++os)) := by
  induction ws generalizing a os with
  | nil => simp only [List.foldl_nil,List.length_nil,Nat.add_zero,List.range'_zero,List.map_nil,
      List.reverse_nil,List.nil_append]
  | cons w ws ih =>
    rw [List.foldl_cons,op_pair,ih]
    simp only [List.length_cons,List.range'_succ,List.map_cons,List.reverse_cons,List.append_assoc,
      List.singleton_append,Nat.add_assoc,Nat.add_comm 1]
lemma range_length (n : ℕ) : (encode ((List.range' 0 n).map Nat.bits)).length ≤ n*(2*n+2) := by
  have hh := encode_le_bound ((List.range' 0 n).map Nat.bits) n (by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    have hh := (List.mem_range'_1.mp hi).2
    exact (bits_length_le i).trans (by omega))
  simpa only [List.length_map,List.length_range'] using hh

lemma run_encode (ws : List (List Bool)) : run (encode ws)=encode ((List.range ws.length).map Nat.bits) := by
  unfold run
  rw [Fold.run_encode op (20*(Polynomial.X+1)^2) [] (pairBits (Nat.bits 0,encode [])) ws
    (2*ws.length+1+ws.length*(2*ws.length+2))]
  · rw [fold_eq,discardPrefix_pairBits,List.append_nil,reverse_encode,List.reverse_reverse,List.range_eq_range']
  · intro n
    rw [fold_eq,Nat.zero_add,List.append_nil,pairBits_length]
    dsimp only
    rw [length_encode_reverse]
    have hb := bits_length_le (ws.take n).length
    have hr := range_length (ws.take n).length
    have hl : (ws.take n).length ≤ ws.length := by simp only [List.length_take]; omega
    nlinarith
  · simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one,Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    have hw := length_le_encode ws
    have hsq := Nat.mul_le_mul hw hw
    nlinarith [Nat.zero_le ((pairBits (Nat.bits 0, encode [])).length)]
end Indices
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundOp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic
namespace NaturalArray
open WordList

lemma sumWords_encode (xs : List ℕ) : sumWords (encode xs)=xs.sum.bits := by
  simp only [sumWords,encode,mapWith_encode,List.map_map,Function.comp_def,signedOp,discardPrefix_pairBits,value_bits]
  have hh := IntegerArray.sumWords_encode (xs.map (fun n : ℕ => (n:ℤ)))
  simp only [IntegerArray.encode,List.map_map,Function.comp_def] at hh
  rw [hh]
  clear hh
  have hs : (xs.map (fun n : ℕ => (n:ℤ))).sum=(xs.sum:ℤ) := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih,Nat.cast_add]
  rw [hs,Signed.encode,List.tail_cons,Int.natAbs_natCast]
end NaturalArray
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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
namespace Drop
open Lookup (step step_computes iterate_bounds step_zero step_succ)
lemma drop_iterate (n i : ℕ) (ws : List (List Bool)) (hn : ws.length≤n) :
    discardPrefix (step^[n] (pairBits (i.bits,encode ws)))=encode (ws.drop i) := by
  induction n generalizing i ws with
  | zero=>
    have hw : ws=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst ws
    simp only [Function.iterate_zero_apply,discardPrefix_pairBits,List.drop_nil]
  | succ n ih=>
    cases i with
    | zero=>rw [Function.iterate_fixed (step_zero ws),discardPrefix_pairBits,List.drop_zero]
    | succ i=>
      rw [Function.iterate_succ_apply,step_succ]
      have hl : ws.tail.length≤n := by simp only [List.length_tail]; omega
      rw [ih i ws.tail hl]
      cases ws with
      | nil=>simp only [List.tail_nil,List.drop_nil]
      | cons w ws=>rfl
lemma run_encode (i : ℕ) (ws : List (List Bool)) :
    run (pairBits (i.bits,encode ws))=encode (ws.drop i) := by
  apply drop_iterate
  have h:=length_le_encode ws
  rw [pairBits_length]
  dsimp only
  omega
end Drop
lemma lengthBits_encode (ws : List (List Bool)) : lengthBits (encode ws)=ws.length.bits := by
  simp only [lengthBits,Function.comp_apply,Count.run_encode,UnaryResources.lengthBits_eq,List.length_replicate]
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordTake
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Take
open WordOperations BinaryArithmetic
attribute [local irreducible] number reverse Drop.run
lemma run_encode (n : ℕ) (ws : List (List Bool)) :
    run (pairBits (n.bits,encode ws))=encode (ws.take n) := by
  simp only [run,number,extractPrefix_pairBits,discardPrefix_pairBits,lengthBits_encode,value_bits,
    reverse_encode,Drop.run_encode,List.reverse_drop,List.reverse_reverse,List.length_reverse]
  congr 1
  rw [show ws.length-(ws.length-n)=min n ws.length by omega]
  exact List.take_eq_take_min.symm
end MetricKMedianRecovery.BitMachine.WordList.Take

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Dyadic.Canonical

lemma findRank_eq (ws : List ℕ) (v : ℕ) : findRank ws v=rank ws v := by
  induction ws generalizing v with
  | nil=>rfl
  | cons w ws ih=>
    by_cases h : v<w
    · simp [findRank,List.range_succ_eq_map,rank,h]
    · have hzero : decide (v<(List.take (0+1) (w::ws)).sum)=false := by
        simpa using h
      unfold findRank
      rw [List.length_cons,List.range_succ_eq_map,List.find?_cons,hzero]
      dsimp only
      rw [List.find?_map]
      have he : ((fun j=>decide (v<(List.take (j+1) (w::ws)).sum)) ∘ Nat.succ)=
          (fun j=>decide (v-w<(ws.take (j+1)).sum)) := by
        funext j
        apply decide_eq_decide.mpr
        change (v<w+(ws.take (j+1)).sum) ↔ _
        omega
      rw [he,rank,ite_eq_right h]
      exact congrArg (Option.map Nat.succ) (ih (v-w))
end MetricKMedianRecovery.Dyadic.Canonical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_InverseCDF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInverseCDF
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Dyadic.Canonical

attribute [local irreducible] Take.run UnaryResources.inc
attribute [local irreducible] prefixCounts NaturalArray.sumWords
attribute [local irreducible] total
lemma predicate_pack (ws : List ℕ) (v j : ℕ) :
    predicate (pairBits (pairBits (NaturalArray.encode ws,v.bits),j.bits))=
      decide (v<(ws.take (j+1)).sum) := by
  simp only [predicate,total,prefixCounts,extractPrefix_pairBits,discardPrefix_pairBits,
    UnaryResources.inc,value_bits,NaturalArray.encode,Take.run_encode,←List.map_take]
  change decide (v<value (NaturalArray.sumWords (NaturalArray.encode (ws.take (j+1)))))=_
  rw [NaturalArray.sumWords_encode,value_bits]
lemma find_pack_s238r_oai (ws : List ℕ) (v : ℕ) :
    find (pairBits (NaturalArray.encode ws,v.bits))=encodeOption (rank ws v) := by
  simp only [find,extractPrefix_pairBits,NaturalArray.encode,Indices.run_encode,List.length_map,Find.run_encode,
    List.find?_map,Function.comp_def]
  have he : (fun j=>predicate (pairBits (pairBits (NaturalArray.encode ws,v.bits),j.bits)))=
      (fun j=>decide (v<(ws.take (j+1)).sum)) := funext (predicate_pack ws v)
  change Find.optionEncode (((List.range ws.length).find? (fun j=>predicate
    (pairBits (pairBits (NaturalArray.encode ws,v.bits),j.bits)))).map Nat.bits)=_
  rw [he]
  change Find.optionEncode ((findRank ws v).map Nat.bits)=_
  rw [findRank_eq]
  cases rank ws v <;> rfl

attribute [local irreducible] searched
end MetricKMedianRecovery.BitMachine.BinaryInverseCDF

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.find_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.find_pack_s238r_oai
