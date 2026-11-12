-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.prepared_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:52:56.575198+00:00
-- url     : https://prove2.me/submissions/3a207917-134e-4b78-956d-0ef78e0268c8

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L030
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidInitial_indices_replicate_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRawOpening_rowWord_pack_s238r

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
namespace MetricKMedianRecovery.BitMachine
open WordOperations
namespace WordList
lemma crossWith_encode (f : List Bool → List Bool) (xs ys : List (List Bool)) :
    crossWith f (pairBits (encode xs,encode ys))=
      encode (xs.flatMap (fun x=>ys.map (fun y=>f (pairBits (x,y))))) := by
  unfold crossWith
  simp only [extractPrefix_pairBits,discardPrefix_pairBits]
  apply flatMapWith_encode
  intro w _
  simp only [extractPrefix_pairBits,discardPrefix_pairBits,mapWith_encode]
lemma cross_encode (xs ys : List (List Bool)) :
    cross (pairBits (encode xs,encode ys))=encode (xs.flatMap (fun x=>ys.map (fun y=>pairBits (x,y)))) :=
  crossWith_encode id xs ys
end WordList
end MetricKMedianRecovery.BitMachine

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
lemma flatMap_ofFn {α β : Type*} {n : ℕ} (f : Fin n → α) (g : α → List β) :
    (List.ofFn f).flatMap g=(List.ofFn (fun j=>g (f j))).flatten := by
  change ((List.ofFn f).map g).flatten=_
  rw [List.map_ofFn]
  rfl
lemma map_encode (f : List Bool → List Bool) (ws : List (List Bool)) :
    map f (encode ws)=encode (ws.map f) := by
  simp only [map,mapWith_encode,Function.comp_apply,discardPrefix_pairBits]
end WordList
namespace BinaryOpeningEnumeration
open WordList EffectiveOpenability RationalOpenability BinaryOpeningPayment

lemma clients_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : clients (pack distances F W v z lam eta i)=
      encode (List.ofFn (fun j : Fin d=>j.val.bits)) := by
  simp only [clients,Function.comp_apply,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,BinaryEllipsoidInitial.indices_replicate_s238r]
lemma kinds_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : kinds (pack distances F W v z lam eta i)=
      encode ((kindRows (List.ofFn (fun j : Fin d=>j)) (subtypeList W) (subtypeList F)).map BinaryOpeningConstant.kindWord) := by
  simp only [kinds,triples,doubles,caps,duals,clients_pack]
  simp only [pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryOpeningActivity.indices,
    List.map_map,Function.comp_def,cross_encode,map_encode,kindRows,List.map_append,List.map_cons,List.map_nil,
    encode_append,List.map_flatMap,List.map_flatten,List.flatMap_map,List.map_map,
    unaryTag,pairTag,tripleTag,dualTag,extractPrefix_pairBits,discardPrefix_pairBits,
    BinaryOpeningConstant.kindWord,List.map_ofFn,flatMap_ofFn]
lemma columns_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : columns (pack distances F W v z lam eta i)=
      encode (((List.ofFn (fun j : Fin d=>j)).map (fun j=>BinaryOpeningCoefficient.variableWord (F:=F) (.inl j)))++
        (subtypeList F).flatMap (fun f=>(List.ofFn (fun a : Fin d=>a)).flatMap (fun a=>
          (List.ofFn (fun j : Fin d=>j)).map (fun j=>BinaryOpeningCoefficient.variableWord (.inr (f,a,j)))))) := by
  simp only [columns,triples,doubles,clients_pack]
  simp only [pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryOpeningActivity.indices,
    List.map_map,Function.comp_def,cross_encode,map_encode,
    encode_append,List.map_flatMap,List.map_flatten,List.flatMap_map,List.map_map,
    unaryTag,variableTag,extractPrefix_pairBits,discardPrefix_pairBits,
    BinaryOpeningCoefficient.variableWord,List.map_ofFn,flatMap_ofFn]
end BinaryOpeningEnumeration
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FnProdEnum
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.EffectiveOpenability
open RationalOpenability
lemma ofFn_prodEnum {α : Type*} {m n : ℕ} (f : Fin m × Fin n → α) :
    List.ofFn (fun i=>f (finProdFinEquiv.symm i))=
      (List.ofFn (fun i : Fin m=>i)).flatMap (fun i=>List.ofFn (fun j : Fin n=>f (i,j))) := by
  rw [List.ofFn_mul]
  change _ = ((List.ofFn (fun i : Fin m=>i)).map (fun i=>List.ofFn (fun j : Fin n=>f (i,j)))).flatten
  rw [List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have he : (⟨i.val*n+j.val,by nlinarith [i.isLt,j.isLt]⟩ : Fin (m*n))=finProdFinEquiv (i,j) := by
    apply Fin.ext
    change i.val*n+j.val=j.val+n*i.val
    ring
  rw [he,Equiv.symm_apply_apply]
lemma ofFn_variableEnum {α : Type*} {m d : ℕ} (F : Finset (Fin m)) (f : Variables (Fin d) F → α) :
    List.ofFn (fun j=>f (variableEnum d F j))=
      (List.ofFn (fun j : Fin d=>j)).map (fun j=>f (.inl j))++
      (subtypeList F).flatMap (fun g=>(List.ofFn (fun a : Fin d=>a)).flatMap (fun a=>
        (List.ofFn (fun j : Fin d=>j)).map (fun j=>f (.inr (g,a,j))))) := by
  let g : Fin (F.card*(d*d)) → α := fun j=>f (.inr ((F.orderIsoOfFin rfl) (finProdFinEquiv.symm j).1,
    finProdFinEquiv.symm (finProdFinEquiv.symm j).2))
  have he : (fun j=>f (variableEnum d F j))=Fin.append (fun j=>f (.inl j)) g := by
    funext j
    refine Fin.addCases (fun k=>?_) (fun k=>?_) j
    · simp [variableEnum]
    · simp [variableEnum,Fin.append_right,g]
  rw [he,List.ofFn_fin_append]
  simp only [List.map_ofFn,Function.comp_def]
  congr 1
  change List.ofFn (fun j=>(fun p=>f (.inr ((F.orderIsoOfFin rfl) p.1,finProdFinEquiv.symm p.2)))
    (finProdFinEquiv.symm j))=_
  rw [ofFn_prodEnum (fun p : Fin F.card × Fin (d*d)=>f (.inr ((F.orderIsoOfFin rfl) p.1,finProdFinEquiv.symm p.2)))]
  simp only [subtypeList,BitMachine.WordList.flatMap_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  rw [ofFn_prodEnum (fun p : Fin d × Fin d=>f (.inr ((F.orderIsoOfFin rfl) j,p)))]
  simp only [BitMachine.WordList.flatMap_ofFn]
end MetricKMedianRecovery.EffectiveOpenability

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RowInput
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRawOpening
open WordOperations BinaryArithmetic WordList RationalLinearFeasibility RationalOpenability EffectiveOpenability
open BinaryOpeningPayment BinaryOpeningEnumeration
lemma columns_source {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : columns (pack distances F W v z lam eta i)=
      encode (List.ofFn (fun j=>BinaryOpeningCoefficient.variableWord (variableEnum d F j))) := by
  rw [columns_pack,ofFn_variableEnum]

lemma rows_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : rows (pack distances F W v z lam eta i)=
      BinaryRow.rowsEncode ((kindRows (List.ofFn (fun j : Fin d=>j)) (subtypeList W) (subtypeList F)).map
        (fun r=>(forms distances F W v z lam eta i r).enumeratedRow (variableEnum d F))) := by
  simp only [rows,kinds_pack,mapWith_encode,List.map_map,Function.comp_def,rowWord_pack_s238r,BinaryRow.rowsEncode]
lemma bound_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : bound (pack distances F W v z lam eta i)=(1+v^2)*z := by
  simp only [bound,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryRational.decode_encode,pow_two]
lemma prepared_pack_s238r_oai {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : prepared (pack distances F W v z lam eta i)=
      BinaryOpeningOracle.pack distances F W v z lam eta i := by
  simp only [prepared,columns_source,kinds_pack,bound_pack,rows_pack,Count.run_encode,List.length_ofFn,
    List.length_map,BinaryOpeningOracle.pack,BinaryRationalDecision.pack]

end MetricKMedianRecovery.BitMachine.BinaryRawOpening

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.prepared_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryRawOpening.prepared_pack_s238r_oai
