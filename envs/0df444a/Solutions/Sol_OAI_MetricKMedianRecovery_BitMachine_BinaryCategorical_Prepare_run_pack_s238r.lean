-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.run_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:01:53.136358+00:00
-- url     : https://prove2.me/submissions/9a6edfc0-c0dd-471e-915f-40a9f6334f7a

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L026
import Definitions.Def_Q238L034
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCategorical_Prepare_left_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySeed_nest_tensor_s238r

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
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyComputes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace UnaryResources
lemma copies_replicate (a b : ℕ) (v : Bool) :
    RepeatedAppend.copies a (List.replicate b v)=List.replicate (a*b) v := by
  induction a with
  | zero => simp only [RepeatedAppend.copies,Nat.zero_mul,List.replicate_zero]
  | succ a ih => rw [RepeatedAppend.copies,ih,←List.replicate_add]; congr 1; ring

end UnaryResources
namespace WordList
lemma copies_encode (n : ℕ) (w : List Bool) :
    RepeatedAppend.copies n (encode [w])=encode (List.replicate n w) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RepeatedAppend.copies,ih,←encode_append,←List.replicate_succ']

lemma repeatWords_pair (u w : List Bool) : repeatWords (pairBits (u,w))=
    encode (List.replicate u.length w) := by
  simp only [repeatWords,extractPrefix_pairBits,discardPrefix_pairBits,copies_encode]
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace NaturalArray
open WordList
lemma product_le (xs : List ℕ) : xs.prod≤2^(xs.map (fun n=>n.bits.length)).sum := by
  induction xs with
  | nil => simp only [List.prod_nil,List.map_nil,List.sum_nil,pow_zero,Nat.le_refl]
  | cons x xs ih =>
    simp only [List.prod_cons,List.map_cons,List.sum_cons,pow_add]
    apply Nat.mul_le_mul _ ih
    have hh := BinarySubtraction.value_lt x.bits
    rw [value_bits] at hh
    exact hh.le
lemma product_length (xs : List ℕ) : xs.prod.bits.length≤(xs.map (fun n=>n.bits.length)).sum+1 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  apply (product_le xs).trans_lt
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)
lemma fold_mul (xs : List ℕ) (a : ℕ) (ctx : List Bool) :
    (xs.map Nat.bits).foldl (Fold.operation mulOp ctx) a.bits=(a*xs.prod).bits := by
  induction xs generalizing a with
  | nil => simp only [List.map_nil,List.foldl_nil,List.prod_nil,mul_one]
  | cons x xs ih =>
    simp only [List.map_cons,List.foldl_cons,Fold.operation,mulOp,
      extractPrefix_pairBits,discardPrefix_pairBits,value_bits,ih,List.prod_cons]
    congr 1
    ring
lemma productWords_encode (xs : List ℕ) : productWords (encode xs)=xs.prod.bits := by
  unfold productWords encode
  rw [Fold.run_encode mulOp (4*Polynomial.X+4) [] (1:ℕ).bits (xs.map Nat.bits)
    (1+(WordList.encode (xs.map Nat.bits)).length)]
  · simp only [fold_mul,one_mul]
  · intro n
    rw [←List.map_take,fold_mul,one_mul]
    have hp := product_length (xs.take n)
    have hl := WordList.length_encode (xs.take n |>.map Nat.bits)
    have ht := WordList.length_encode_take (xs.map Nat.bits) n
    rw [←List.map_take] at ht
    simp only [List.map_map,Function.comp_def] at hl
    omega
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega

lemma exponentiate_pair (u : List Bool) (a : ℕ) : exponentiate (pairBits (u,a.bits))=(a^u.length).bits := by
  rw [exponentiate,repeatWords_pair]
  have he : WordList.encode (List.replicate u.length a.bits)=encode (List.replicate u.length a) := by
    simp only [encode,List.map_replicate]
  rw [he,productWords_encode,List.prod_replicate]

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
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_TensorEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
lemma count_eq (ds : List ℕ) (b : ℕ) : count ds b=(ds++[b]).prod := by
  induction ds with
  | nil=>simp [count]
  | cons n ns ih=>simp only [count,List.cons_append,List.prod_cons,ih]
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape
open BinarySeed
variable (q a b L : ℕ)
lemma raw_left_length (bits : Categorical.BinaryOracleIndex (Fin q) a b L→Bool) :
    (BinarySeed.raw ((tensors q a b L bits).1)).length=M q a b L := by
  rw [BinarySeed.raw_length,←count_eq]
lemma parsed_right (bits : Categorical.BinaryOracleIndex (Fin q) a b L→Bool) :
    BinarySeed.parsed ((tensors q a b L bits).2)=
      seedBits ((Categorical.binarySeedEquiv (Fin q) a b L bits).2) := rfl
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Tape

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources
open WordOperations WordList BinaryArithmetic
open Categorical.Explicit

lemma bword_pack (q a : ℕ) : bword (pack q a)=List.replicate (exponent a) true := by
  simp only [bword,pack,discardPrefix_pairBits,UnaryResources.lengthBits_eq,List.length_replicate,
    UnaryResources.inc,value_bits,RawUnary.run,Nat.size_eq_bits_len,UnaryResources.copies_replicate,
    ←List.replicate_add,exponent]
lemma tbits_pack (q a : ℕ) : tbits (pack q a)=(steps a).bits := by
  rw [tbits,bword_pack,NaturalArray.exponentiate_pair,List.length_replicate]; rfl
attribute [local irreducible] bword tbits RawTake.run RawUnary.run NaturalArray.exponentiate
attribute [local irreducible] qnext anext
attribute [local irreducible] factor
lemma lbits_pack (q a : ℕ) : lbits (pack q a)=(samples q a).bits := by
  rw [lbits,factor,tbits_pack]
  simp only [qnext,anext,pack,extractPrefix_pairBits,discardPrefix_pairBits,UnaryResources.lengthBits_eq,
    List.length_replicate,UnaryResources.inc,value_bits,samples]
lemma cap_length (x : List Bool) : (cap.word x).length=4096000000000*(x.length+2)^5 := by
  rw [cap.word_length]; simp only [capPoly,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X]
attribute [local irreducible] cap
lemma unary_eq {w : List Bool→List Bool} {x : List Bool} {n : ℕ} (hw : w x=n.bits)
    (hn : n≤4096000000000*(x.length+2)^5) : unary w x=List.replicate n true := by
  rw [unary,hw,RawTake.run_pack]
  simp only [RawUnary.run,List.length_take,cap_length,Nat.min_eq_left hn]
lemma dimensions (q a : ℕ) : q≤(pack q a).length ∧ a≤(pack q a).length := by
  simp only [pack,pairBits,List.length_append,List.length_flatMap,List.length_cons,List.length_nil,
    List.map_const',List.sum_replicate,List.length_replicate,smul_eq_mul]
  omega
lemma sample_bound (q a : ℕ) : samples q a ≤4096000000000*((pack q a).length+2)^5 := by
  obtain ⟨hq,ha⟩:=dimensions q a
  have ht:=steps_upper a
  unfold samples
  calc
    _ ≤ 1000000000*(4096*((pack q a).length+2)^2)*((pack q a).length+2)*((pack q a).length+2)^2 := by
      apply Nat.mul_le_mul
      · apply Nat.mul_le_mul
        · apply Nat.mul_le_mul_left
          exact ht.trans (by gcongr)
        · omega
      · gcongr; omega
    _ = _ := by ring
lemma lword_pack (q a : ℕ) : lword (pack q a)=List.replicate (samples q a) true := unary_eq (lbits_pack q a) (sample_bound q a)
lemma tword_pack (q a : ℕ) : tword (pack q a)=List.replicate (steps a) true := by
  apply unary_eq (tbits_pack q a)
  apply le_trans _ (sample_bound q a)
  unfold samples
  have hs:1≤(q+1)*(a+1)^2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc
    steps a = steps a*1 := by omega
    _ ≤ steps a*((q+1)*(a+1)^2) := Nat.mul_le_mul_left _ hs
    _ ≤ 1000000000*steps a*(q+1)*(a+1)^2 := by nlinarith
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Resources

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CategoricalRawPrep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
open Categorical.Explicit
variable {q a : ℕ}
attribute [local irreducible] Resources.tword Resources.lword Resources.bword dimensions
attribute [local irreducible] BinarySeed.product leftShape
attribute [local irreducible] BinarySeed.nest RawTake.run RawDrop.run cut rightShape tword lword bword
section Correct
variable (ctx : List Bool) (part : Fin q→Fin a)
  (bits : Categorical.BinaryOracleIndex (Fin q) a (exponent a) (samples q a)→Bool)
local notation "xx" => pack ctx part bits
lemma qword_pack : qword xx=List.replicate q true := by
  simp only [qword,pack,extractPrefix_pairBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,partBits,Count.run_encode,List.length_ofFn]
lemma aword_pack : aword xx=List.replicate a true := by
  simp only [aword,pack,extractPrefix_pairBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma dimensions_pack : dimensions xx=Resources.pack q a := by rw [dimensions,qword_pack,aword_pack]; rfl
lemma tword_pack : tword xx=List.replicate (steps a) true := by rw [tword,dimensions_pack,Resources.tword_pack]
lemma leftShape_pack : leftShape xx=BinarySeed.shape [steps a,q,samples q a,a,exponent a] := by
  rw [leftShape,tword_pack,qword_pack,lword,dimensions_pack,Resources.lword_pack,aword_pack,bword,dimensions_pack,Resources.bword_pack]; rfl
lemma rightShape_pack : rightShape xx=BinarySeed.shape [a,exponent a] := by
  rw [rightShape,aword_pack,bword,dimensions_pack,Resources.bword_pack]; rfl
lemma cut_pack : cut xx=(Tape.M q a (exponent a) (samples q a)).bits := by
  rw [cut,leftShape_pack]
  change BinarySeed.product [steps a,q,samples q a,a,exponent a].length (BinarySeed.shape _) = _
  rw [BinarySeed.product_shape]
  congr 1
  simp only [Tape.M,BinarySeed.count,steps,List.prod_cons,List.prod_nil,Nat.mul_one]
lemma right_pack : right xx=seedBits ((Categorical.binarySeedEquiv (Fin q) a (exponent a) (samples q a) bits).2) := by
  rw [right,rightShape_pack,cut_pack]
  simp only [pack,discardPrefix_pairBits,RawDrop.run_encode,Tape.raw,←Tape.raw_left_length q a (exponent a) (samples q a) bits,List.drop_left]
  change BinarySeed.nest [a].length (pairBits (BinarySeed.shape ([a]++[exponent a]),_)) = _
  rw [BinarySeed.nest_tensor_s238r,Tape.parsed_right]
lemma run_pack_s238r_oai : run xx=outputPack ctx part (Categorical.binarySeedEquiv (Fin q) a (exponent a) (samples q a) bits) := by
  rw [run,runInput,aword_pack,tword_pack,left_pack_s238r,right_pack]
  simp only [pack,extractPrefix_pairBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,outputPack,runPack,List.map_ofFn,Function.comp_def,steps]
end Correct
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.run_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.run_pack_s238r_oai
