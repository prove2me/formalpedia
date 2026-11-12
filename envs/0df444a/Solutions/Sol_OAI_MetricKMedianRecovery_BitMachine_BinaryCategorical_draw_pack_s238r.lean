-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:38:13.636972+00:00
-- url     : https://prove2.me/submissions/5c213b3c-9648-4469-b9c4-cc81082a9b4d

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
lemma length_encode_zip (xs ys : List (List Bool)) :
    (encode ((xs.zip ys).map pairBits)).length ≤ 2*(encode xs).length+(encode ys).length := by
  induction xs generalizing ys with
  | nil => simp only [List.zip_nil_left,List.map_nil,encode,List.length_nil,Nat.zero_le]
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.zip_nil_right,List.map_nil,encode,List.length_nil,Nat.zero_le]
    | cons y ys =>
      simp only [List.zip_cons_cons,List.map_cons,encode,length_cons,pairBits_length]
      have h := ih ys
      omega
namespace Zip

lemma op_nil (w : List Bool) (os : List (List Bool)) :
    Fold.operation op [] (pairBits (encode [],encode os)) w=pairBits (encode [],encode os) := by
  simp only [Fold.operation,op,extractPrefix_pairBits,discardPrefix_pairBits,encode,ite_true, if_true]
lemma op_cons (w y : List Bool) (ys os : List (List Bool)) :
    Fold.operation op [] (pairBits (encode (y::ys),encode os)) w=
      pairBits (encode ys,encode (pairBits (w,y)::os)) := by
  simp only [Fold.operation,op,extractPrefix_pairBits,discardPrefix_pairBits,encode,cons_ne_nil,ite_false, if_false,
    tail_cons,head_cons]
lemma fold_eq (xs ys os : List (List Bool)) :
    xs.foldl (Fold.operation op []) (pairBits (encode ys,encode os))=
      pairBits (encode (ys.drop xs.length),encode (((xs.zip ys).map pairBits).reverse++os)) := by
  induction xs generalizing ys os with
  | nil => simp only [List.foldl_nil,List.length_nil,List.drop_zero,List.zip_nil_left,List.map_nil,
      List.reverse_nil,List.nil_append]
  | cons x xs ih =>
    rw [List.foldl_cons]
    cases ys with
    | nil =>
      rw [op_nil,ih]
      simp only [List.drop_nil,List.zip_nil_right,List.map_nil,List.reverse_nil,List.nil_append]
    | cons y ys =>
      rw [op_cons,ih]
      simp only [List.length_cons,List.drop_succ_cons,List.zip_cons_cons,List.map_cons,List.reverse_cons,
        List.append_assoc,List.singleton_append]

lemma run_encode (xs ys : List (List Bool)) :
    run (pairBits (encode xs,encode ys))=encode ((xs.zip ys).map pairBits) := by
  unfold run
  rw [extractPrefix_pairBits,discardPrefix_pairBits]
  change reverse (discardPrefix (Fold.run op _ (Fold.pack (encode xs) [] (pairBits (encode ys,encode [])))))=_
  rw [Fold.run_encode op (4*Polynomial.X+4) [] (pairBits (encode ys,encode [])) xs
    (2*(encode xs).length+3*(encode ys).length+1)]
  · rw [fold_eq,discardPrefix_pairBits,List.append_nil,reverse_encode,List.reverse_reverse]
  · intro n
    rw [fold_eq,List.append_nil,pairBits_length]
    dsimp only
    have hd := length_encode_drop ys (xs.take n).length
    have hz := length_encode_zip (xs.take n) ys
    have ht := length_encode_take xs n
    rw [length_encode_reverse]
    omega
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero,pairBits_length,encode]
    omega
end Zip
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
lemma mapWith_ofFn {n : ℕ} (f : List Bool → List Bool) (d : List Bool) (g : Fin n → List Bool) :
    mapWith f (pairBits (d,encode (List.ofFn g)))=encode (List.ofFn (fun i=>f (pairBits (d,g i)))) := by
  rw [mapWith_encode,List.map_ofFn]
  rfl
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NumAbs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open WordOperations BinaryArithmetic
open scoped Matrix
namespace WordList
lemma zip_ofFn {n : ℕ} {α β : Type*} (u : Fin n → α) (v : Fin n → β) :
    (List.ofFn u).zip (List.ofFn v)=List.ofFn (fun i=>(u i,v i)) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_zip,List.getElem_ofFn]
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
end Flatten
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
variable {E : Type*} {a T : ℕ}
lemma drawPick_pack (enc : E→List Bool) (r : Fin a→Fin T→Option E) (s : Fin a→Fin T) (skip : ℕ) (j : Fin a) :
    drawPick (pairBits (drawPack enc r s skip,pairBits (j.val.bits,(s j).val.bits)))=
      optionBits enc (omitted r skip j (s j)) := by
  simp only [drawPick,drawRow,drawPack,tableBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,extractPrefix_pairBits,discardPrefix_pairBits,value_bits,lookup_ofFn,omitted]
  split_ifs <;> rfl
lemma drawItems_pack (enc : E→List Bool) (r : Fin a→Fin T→Option E) (s : Fin a→Fin T) (skip : ℕ) :
    drawItems (drawPack enc r s skip)=encode (List.ofFn (fun j=>pairBits (j.val.bits,(s j).val.bits))) := by
  simp only [drawItems,drawPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,seedBits,indices_ofFn,Zip.run_encode,zip_ofFn,List.map_ofFn,Function.comp_def]
lemma encode_flatten (wss : List (List (List Bool))) : encode wss.flatten=(wss.map encode).flatten := by
  induction wss with
  | nil=>rfl
  | cons ws wss ih=>simp only [List.flatten_cons,encode_append,List.map_cons,ih]
lemma draw_pack_s238r_oai (enc : E→List Bool) (r : Fin a→Fin T→Option E) (s : Fin a→Fin T) (skip : ℕ) :
    draw (drawPack enc r s skip)=encode ((drawn (omitted r skip) s).map enc) := by
  rw [draw,drawItems_pack]
  simp only [flatMapWith,Function.comp_apply,mapWith_ofFn,drawPick_pack,optionBits,Flatten.run_encode,
    drawn,List.map_flatten,encode_flatten,List.map_ofFn,Function.comp_def]
attribute [local irreducible] Set.run mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_pack_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_pack_s238r_oai.{u_1}
