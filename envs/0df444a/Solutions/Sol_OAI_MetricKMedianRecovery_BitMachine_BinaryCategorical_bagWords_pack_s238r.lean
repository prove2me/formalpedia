-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagWords_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:38:12.571401+00:00
-- url     : https://prove2.me/submissions/f675a797-0dda-4b80-b524-fb3103017e1a

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L024
import Definitions.Def_Q238L026

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RowEncode
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
lemma lookup_ofFn {n : ℕ} (i : Fin n) (f : Fin n → List Bool) :
    Lookup.run (pairBits (i.val.bits,encode (List.ofFn f)))=f i := by
  rw [Lookup.run_encode]
  simp only [List.getElem?_ofFn,i.isLt,dite_eq_left,Option.getD_some]
lemma indices_ofFn {n : ℕ} (f : Fin n → List Bool) :
    Indices.run (encode (List.ofFn f))=encode (List.ofFn (fun i : Fin n=>i.val.bits)) := by
  rw [Indices.run_encode,List.length_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
end WordList
end MetricKMedianRecovery.BitMachine

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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalScore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
variable {q a T L : ℕ}
attribute [local irreducible] mapWith
lemma elementPart_pack (ctx : List Bool) (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q))
    (seed : Categorical.OracleSeed (Fin q) a T L) (e : Fin q) :
    elementPart (pairBits (scorePack ctx part r seed,elemBits e))=(part e).val.bits := by
  simp only [elementPart,scorePack,elemBits,partBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,extractPrefix_pairBits,discardPrefix_pairBits,lookup_ofFn]
end MetricKMedianRecovery.BitMachine.BinaryCategorical

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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
variable {q a T L : ℕ}
lemma bagTest_pack (ctx : List Bool) (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q))
    (seed : Categorical.OracleSeed (Fin q) a T L) (j : Fin a) (e : Fin q) :
    bagTest (pairBits (pairBits (scorePack ctx part r seed,j.val.bits),elemBits e))=decide (part e=j) := by
  simp only [bagTest,extractPrefix_pairBits,discardPrefix_pairBits,elementPart_pack,value_bits]
  exact decide_eq_decide.mpr ⟨Fin.ext,fun h=>congrArg Fin.val h⟩
lemma bagWords_pack_s238r_oai (ctx : List Bool) (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q))
    (seed : Categorical.OracleSeed (Fin q) a T L) (j : Fin a) :
    bagWords (pairBits (scorePack ctx part r seed,j.val.bits))=
      encode ((Categorical.Selected.bag (elements q) part j).map elemBits) := by
  unfold bagWords
  have hfield : field 3 (extractPrefix (pairBits (scorePack ctx part r seed,j.val.bits)))=partBits part := by
    simp only [extractPrefix_pairBits,scorePack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some]
  rw [hfield]
  simp only [partBits,indices_ofFn]
  rw [show List.ofFn (fun i : Fin q=>i.val.bits)=(elements q).map elemBits by
    simp only [elements,List.map_ofFn,Function.comp_def,elemBits,id_eq]]
  rw [filterWith_encode,List.filter_map]
  simp only [Function.comp_def,bagTest_pack,Categorical.Selected.bag]
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagWords_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagWords_pack_s238r_oai
