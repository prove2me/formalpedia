-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:45:54.127856+00:00
-- url     : https://prove2.me/submissions/019d1cb0-81f6-49ab-b56d-abad1a882ad8

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L028
import Definitions.Def_Q238L029
import Definitions.Def_Q238L031
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidInitial_indices_replicate_s238r

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalMatrix
open WordList

lemma rowEncode_eq {n : ℕ} (v : Fin n → ℚ) :
    rowEncode v=WordList.encode (List.ofFn (fun i=>BinaryRational.encode (v i))) := by
  simp only [rowEncode,RationalArray.encode,List.map_ofFn,Function.comp_def]

end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack7
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryEllipsoidInitial
open RationalMatrix WordList

lemma entryWords_pack (n : ℕ) (q : ℚ) (i j : Fin n) :
    entryWords (pairBits (pairBits (pack n q,i.val.bits),j.val.bits))=
      BinaryRational.encode ((q • (1:Matrix (Fin n) (Fin n) ℚ)) i j) := by
  simp only [entryWords,ctx,row,col,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    pack,value_bits,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
  by_cases hij : i=j
  · subst j; simp
  · have hh : i.val≠j.val := fun h=>hij (Fin.ext h)
    split_ifs <;> simp_all; omega

lemma rowWords_pack (n : ℕ) (q : ℚ) (i : Fin n) :
    rowWords (pairBits (pack n q,i.val.bits))=
      rowEncode ((q • (1:Matrix (Fin n) (Fin n) ℚ)) i) := by
  simp only [rowWords,Function.comp_apply,rowInput,extractPrefix_pairBits,pack,indices_replicate_s238r,mapWith_ofFn]
  change WordList.encode (List.ofFn (fun j=>entryWords (pairBits (pairBits (pack n q,i.val.bits),j.val.bits))))=_
  simp only [entryWords_pack,rowEncode_eq]

lemma run_pack (n : ℕ) (q : ℚ) : run (pack n q)=
    RationalMatrix.encode (q • (1:Matrix (Fin n) (Fin n) ℚ)) := by
  simp only [run,Function.comp_apply,runInput,pack,extractPrefix_pairBits,indices_replicate_s238r,mapWith_ofFn]
  change WordList.encode (List.ofFn (fun i=>rowWords (pairBits (pack n q,i.val.bits))))=_
  simp only [rowWords_pack,RationalMatrix.encode]

end BinaryEllipsoidInitial
end
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid RationalHeight
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode3
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
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

lemma factorial_list (n : ℕ) : ((List.range n).map (fun i=>i+1)).prod=n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ,List.map_append,List.prod_append,ih]; simp [Nat.factorial_succ,mul_comm]
lemma factorialWords_replicate (n : ℕ) : factorialWords (List.replicate n true)=n.factorial.bits := by
  simp only [factorialWords,BinaryEllipsoidInitial.indices,BinaryEllipsoidInitial.dummy,
    Function.comp_apply,repeatWords_pair,List.length_replicate,Indices.run_encode,List.length_replicate]
  rw [mapWith_encode]
  simp only [List.map_map,Function.comp_def,nextOp,discardPrefix_pairBits,UnaryResources.inc,value_bits]
  simpa only [encode,List.map_map,Function.comp_def,factorial_list] using
    productWords_encode ((List.range n).map (fun i=>i+1))

lemma bits_length_log (n : ℕ) (hn : n≠0) : n.bits.length=n.log2+1 := by
  rw [Nat.size_eq_bits_len]
  have hl := Nat.size_le.mpr (Nat.lt_log2_self (n:=n))
  have hh := (Nat.log2_lt hn).mpr (Nat.lt_size_self n)
  omega
lemma unaryLog_bits (n : ℕ) : unaryLog n.bits=List.replicate (n.log2+1) true := by
  simp only [unaryLog,value_bits,BinaryArithmetic.normalize_eq_bits]
  by_cases hn : n=0
  · subst n; rfl
  · rw [ite_eq_right hn]
    change RepeatedAppend.copies n.bits.length (List.replicate 1 true)=_
    rw [UnaryResources.copies_replicate,Nat.mul_one,bits_length_log n hn]
end NaturalArray
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryDecision
open UnaryResources NaturalArray

lemma projections_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    nword (pack A b B H)=List.replicate n true ∧ mword (pack A b B H)=List.replicate m true ∧
    bound (pack A b B H)=B.bits ∧ height (pack A b B H)=H.bits ∧
    rows (pack A b B H)=BinaryRow.rowsEncode (List.ofFn (fun r=>integerRow (A r) (b r))) := by
  simp only [pack,nword,mword,rest₁,rest₂,rest₃,bound,height,rows,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits,and_self]
lemma dim_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) : dim (pack A b B H)=n.bits := by
  rw [dim,Function.comp_apply,lengthBits_eq,(projections_pack A b B H).1,List.length_replicate]
lemma count_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) : count (pack A b B H)=m.bits := by
  rw [count,Function.comp_apply,lengthBits_eq,(projections_pack A b B H).2.1,List.length_replicate]

lemma nextDim_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    nextDim (pack A b B H)=List.replicate (n+1) true := by
  rw [nextDim,(projections_pack A b B H).1,List.replicate_succ']
lemma gap_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    gap (pack A b B H)=(gapDenominator m n H).bits := by
  simp only [gap,factorial,Function.comp_apply,nextDim_pack,factorialWords_replicate,power,base,
    rowFactor,count_pack,dim_pack,(projections_pack A b B H).2.2.2.1,value_bits]
  rw [exponentiate_pair,List.length_replicate,value_bits]
  simp only [gapDenominator,pow_two]
lemma epsilon_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    epsilon (pack A b B H)=BinaryRational.encode (gapEpsilon m n H) := by
  simp only [epsilon,doubledGap,gap_pack,value_bits,gapEpsilon,Nat.cast_mul,Nat.cast_ofNat]
lemma precision_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    precision (pack A b B H)=List.replicate (precisionLog m n H) true := by
  simp only [precision,Function.comp_apply,precisionArg,doubledGap,gap_pack,
    (projections_pack A b B H).2.2.2.1,value_bits,unaryLog_bits,precisionLog]
lemma radius_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    radius (pack A b B H)=(n*(B+1)).bits := by
  simp only [radius,dim_pack,(projections_pack A b B H).2.2.1,value_bits]
lemma radiusPrecision_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    radiusPrecision (pack A b B H)=List.replicate (radiusLog n B) true := by
  simp only [radiusPrecision,Function.comp_apply,radius_pack,unaryLog_bits,radiusLog]
end BinaryDecision
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundOp
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryDecision
open WordList RationalMatrix

lemma boundOp_pair {n : ℕ} (b : ℚ) (a : Fin n → ℚ) :
    boundOp (pairBits (BinaryRational.encode b,rowEncode a))=BinaryRow.encode ⟨a,b⟩ := by
  simp only [boundOp,extractPrefix_pairBits,discardPrefix_pairBits,BinaryRow.encode]
lemma boxShape_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) (s : Bool) :
    boxShape s (pack A b B H)=RationalMatrix.encode (fun i j=>(boundedMatrix A (.inr (s,i)) j:ℚ)) := by
  rw [boxShape,(projections_pack A b B H).1]
  change BinaryEllipsoidInitial.run (BinaryEllipsoidInitial.pack n (if s then 1 else -1))=_
  rw [BinaryEllipsoidInitial.run_pack]
  congr 1
  ext i j
  simp only [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,boundedMatrix]
  by_cases hij : i=j
  · subst j; cases s <;> simp
  · have hji : j≠i := Ne.symm hij
    simp only [hij,hji,ite_false, if_false,Int.cast_zero,mul_zero]
lemma boxWords_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) (s : Bool) :
    boxWords s (pack A b B H)=BinaryRow.rowsEncode (List.ofFn (fun i=>integerRow (boundedMatrix A (.inr (s,i))) B)) := by
  simp only [boxWords,(projections_pack A b B H).2.2.1,value_bits,boxShape_pack,RationalMatrix.encode,
    mapWith_ofFn,boundOp_pair,BinaryRow.rowsEncode,List.map_ofFn,Function.comp_def,integerRow,Int.cast_natCast]
lemma boundedWords_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    boundedWords (pack A b B H)=BinaryRow.rowsEncode (boundedRows A b B) := by
  simp only [boundedWords,(projections_pack A b B H).2.2.2.2,boxWords_pack,
    boundedRows,BinaryRow.rowsEncode,List.map_append,encode_append]

lemma relaxedOp_pair {n : ℕ} (eps : ℚ) (r : Row n) :
    relaxedOp (pairBits (BinaryRational.encode eps,BinaryRow.encode r))=BinaryRow.encode (relaxedRow eps r) := by
  simp only [relaxedOp,BinaryRow.encode,extractPrefix_pairBits,discardPrefix_pairBits,
    BinaryRational.decode_encode,relaxedRow]
lemma relaxedWords_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    relaxedWords (pack A b B H)=BinaryRow.rowsEncode (relaxedRows (gapEpsilon m n H) (boundedRows A b B)) := by
  simp only [relaxedWords,epsilon_pack,boundedWords_pack,BinaryRow.rowsEncode,mapWith_encode,
    List.map_map,Function.comp_def,relaxedOp_pair,relaxedRows]
lemma prepared_pack_s238r_oai {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    prepared (pack A b B H)=BinaryWeakSolve.pack n (precisionLog m n H) (radiusLog n B) (n*(B+1))
      (relaxedRows (gapEpsilon m n H) (boundedRows A b B)) := by
  simp only [prepared,(projections_pack A b B H).1,precision_pack,radiusPrecision_pack,radius_pack,
    relaxedWords_pack,BinaryWeakSolve.pack]
end BinaryDecision
end
open WordOperations BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared_pack_s238r_oai
