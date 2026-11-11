-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinarySeed.nest_tensor_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:04:13.830213+00:00
-- url     : https://prove2.me/submissions/55b8f4a5-8576-474d-815f-9263bb1a40d1

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K022
import Definitions.Def_Q238K037
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidInitial_indices_replicate_s238

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
lemma mapWith_ofFn {n : ℕ} (f : List Bool → List Bool) (d : List Bool) (g : Fin n → List Bool) :
    mapWith f (pairBits (d,encode (List.ofFn g)))=encode (List.ofFn (fun i=>f (pairBits (d,g i)))) := by
  rw [mapWith_encode,List.map_ofFn]
  rfl
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_MatrixRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows
open WordOperations WordList BinaryArithmetic
lemma slice_flatten {α : Type*} (xs : List (List α)) (n : ℕ) (h : ∀ x∈xs,x.length=n) (i : ℕ) :
    (xs.flatten.drop (n*i)).take n=(xs[i]?).getD [] := by
  induction xs generalizing i with
  | nil=>simp only [List.flatten_nil,List.drop_nil,List.take_nil,List.getElem?_nil,Option.getD_none]
  | cons x xs ih=>
    have hx:=h x List.mem_cons_self
    have ht : ∀ y∈xs,y.length=n := fun y hy=>h y (List.mem_cons_of_mem _ hy)
    cases i with
    | zero=>simp only [Nat.mul_zero,List.drop_zero,List.flatten_cons,List.getElem?_cons_zero,Option.getD_some]; rw [←hx,List.take_left]
    | succ i=>
      rw [Nat.mul_succ,Nat.add_comm,←List.drop_drop,List.flatten_cons,←hx,List.drop_left]
      simpa only [hx,List.getElem?_cons_succ] using ih ht i
attribute [local irreducible] Drop.run Take.run
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryInputParser.Rows

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_UniformWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
open WordOperations BinaryArithmetic
lemma uniform_value (b : ℕ) (s : Fin b→Bool) :
    value (List.ofFn s).reverse=(Categorical.uniformBits b s).val := by
  induction b with
  | zero=>rfl
  | succ b ih=>
    rw [List.ofFn_succ,List.reverse_cons,value_append,List.length_reverse,List.length_ofFn,ih]
    simp only [value,Nat.mul_zero,Nat.add_zero]
    cases hs : s 0 <;> simp [Categorical.uniformBits,Equiv.trans_apply,Fin.consEquiv,finTwoEquiv,finProdFinEquiv,hs] <;> rfl
lemma normalizeBig_ofFn (b : ℕ) (s : Fin b→Bool) :
    normalizeBig (List.ofFn s)=(Categorical.uniformBits b s).val.bits := by rw [normalizeBig,normalize_eq_bits,uniform_value]
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawSlices
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.RawDrop
open WordOperations BinaryArithmetic

lemma step_zero (ws : List Bool) : step (pairBits (Nat.bits 0,ws))=pairBits (Nat.bits 0,ws) := by
  simp only [step,extractPrefix_pairBits,value_bits,ite_true, if_true]
lemma step_succ (i : ℕ) (ws : List Bool) :
    step (pairBits ((i+1).bits,ws))=pairBits (i.bits,ws.tail) := by
  simp only [step,extractPrefix_pairBits,discardPrefix_pairBits,value_bits,Nat.add_sub_cancel,
    Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false, if_false]
lemma drop_iterate (n i : ℕ) (ws : List Bool) (hn : ws.length≤n) :
    discardPrefix (step^[n] (pairBits (i.bits,ws)))=ws.drop i := by
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
lemma run_encode (i : ℕ) (ws : List Bool) :
    run (pairBits (i.bits,ws))=ws.drop i := by
  apply drop_iterate
  rw [pairBits_length]
  dsimp only
  omega
end MetricKMedianRecovery.BitMachine.RawDrop
namespace MetricKMedianRecovery.BitMachine.RawTake
open WordOperations BinaryArithmetic
attribute [local irreducible] number RawDrop.run
lemma run_pack (n : ℕ) (ws : List Bool) : run (pairBits (n.bits,ws))=ws.take n := by
  simp only [run,number,extractPrefix_pairBits,discardPrefix_pairBits,UnaryResources.lengthBits_eq,value_bits,
    RawDrop.run_encode,List.reverse_drop,List.reverse_reverse,List.length_reverse]
  rw [show ws.length-(ws.length-n)=min n ws.length by omega]
  exact List.take_eq_take_min.symm
end MetricKMedianRecovery.BitMachine.RawTake

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SeedTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
open WordOperations WordList BinaryArithmetic
lemma shape_tail (n : ℕ) (ns : List ℕ) : WordList.tail (shape (n::ns))=shape ns := by
  simp only [shape,List.map_cons,encode,tail_cons]
lemma product_shape (ds : List ℕ) : product ds.length (shape ds)=ds.prod.bits := by
  induction ds with
  | nil=>rfl
  | cons d ds ih=>simp only [List.length_cons,product,shape,List.map_cons,encode,head_cons,tail_cons,
      UnaryResources.lengthBits_eq,List.length_replicate,value_bits,List.prod_cons] at ih ⊢; rw [ih,value_bits]
attribute [local irreducible] width RawTake.run RawDrop.run
lemma raw_length {ds : List ℕ} {b : ℕ} (s : Tensor ds b) : (raw s).length=(ds++[b]).prod := by
  induction ds with
  | nil=>change (List.ofFn (s:Fin b→Bool)).length = b*1
         rw [Nat.mul_one]
         exact List.length_ofFn
  | cons n ns ih=>
    change (List.ofFn (fun i:Fin n=>raw (s i))).flatten.length = ((n::ns)++[b]).prod
    simp only [List.length_flatten,List.map_ofFn,Function.comp_def,ih,List.cons_append,List.prod_cons]
    rw [List.sum_ofFn]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
lemma chunk_tensor (n : ℕ) (ns : List ℕ) (b : ℕ) (s : Tensor (n::ns) b) (i : Fin n) :
    chunk ns.length (pairBits (pairBits (shape (n::ns++[b]),raw s),i.val.bits))=raw (s i) := by
  have hw : width ns.length (pairBits (pairBits (shape (n::ns++[b]),raw s),i.val.bits))=(ns++[b]).prod.bits := by
    rw [width,extractPrefix_pairBits,extractPrefix_pairBits,List.cons_append,shape_tail]
    rw [show ns.length+1=(ns++[b]).length by simp,product_shape]
  rw [chunk,hw,discardPrefix_pairBits,value_bits,extractPrefix_pairBits,discardPrefix_pairBits,
    RawDrop.run_encode,RawTake.run_pack]
  rw [value_bits]
  change ((List.ofFn (fun j=>raw (s j))).flatten.drop ((ns++[b]).prod*i.val)).take (ns++[b]).prod=raw (s i)
  rw [BinaryInputParser.Rows.slice_flatten _ _ (by
    intro x hx; obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hx; exact raw_length (s j)),List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some]
lemma nest_tensor_s238_oai {ds : List ℕ} {b : ℕ} (s : Tensor ds b) :
    nest ds.length (pairBits (shape (ds++[b]),raw s))=parsed s := by
  induction ds with
  | nil=>simpa only [List.length_nil,nest,discardPrefix_pairBits,raw,parsed] using normalizeBig_ofFn b s
  | cons n ns ih=>
    simp only [List.length_cons,nest,indices,extractPrefix_pairBits,shape,List.cons_append,List.map_cons,
      encode,head_cons,BinaryEllipsoidInitial.indices_replicate_s238,mapWith_ofFn]
    change encode (List.ofFn (fun i:Fin n=>nest ns.length (child ns.length
      (pairBits (pairBits (shape (n::ns++[b]),raw s),i.val.bits)))))=encode (List.ofFn (fun i=>parsed (s i)))
    congr 1
    apply congrArg List.ofFn
    funext i
    rw [child,chunk_tensor]
    rw [extractPrefix_pairBits,extractPrefix_pairBits,List.cons_append,shape_tail]
    exact ih (s i)
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinarySeed.nest_tensor_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinarySeed.nest_tensor_s238_oai
