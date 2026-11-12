-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:46:30.935668+00:00
-- url     : https://prove2.me/submissions/29c3cb4c-d847-4f13-8df2-05faa638f8b3

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L028
import Definitions.Def_Q238L029
import Definitions.Def_Q238L031
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryDecision_prepared_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidAdvance_found_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidInitial_indices_replicate_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidIteration_run_pack_s238r

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

lemma triple_iter (j : ℕ) : triple^[j] (1:ℕ).bits=(3^j).bits := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih]; simp only [triple,value_bits,pow_succ']
lemma three_power_length (j : ℕ) : (3^j).bits.length≤2*j+1 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  calc
    3^j ≤ (2^2)^j := Nat.pow_le_pow_left (by norm_num) j
    _ = 2^(2*j) := by rw [pow_mul]
    _ < 2^(2*j+1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
lemma threePower_eq (x : List Bool) : threePower x=(3^x.length).bits := by
  unfold threePower
  rw [BoundedIteration.run_eq,triple_iter]
  intro j hj
  rw [triple_iter,cap_length]
  exact (three_power_length j).trans (by omega)
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
lemma repeatWords_ofFn (n : ℕ) (w : List Bool) : repeatWords (pairBits (List.replicate n true,w))=
    encode (List.ofFn (fun _ : Fin n=>w)) := by
  rw [repeatWords_pair,List.length_replicate,List.ofFn_const]
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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_OptionEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace BinaryEllipsoidAdvance
open Ellipsoid RationalMatrix
open scoped Matrix

lemma stored_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) : stored (pack D rs S)=stateEncode S := by
  simp only [stored,rest₂,rest,Function.comp_apply,pack,discardPrefix_pairBits]
lemma center_pack {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) : center (pack D rs S)=rowEncode S.center := by
  simp only [center,Function.comp_apply,stored_pack,stateEncode,discardPrefix_pairBits]
end BinaryEllipsoidAdvance
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

lemma zeroVector_replicate (n : ℕ) : zeroVector (List.replicate n true)=rowEncode (0 : Fin n → ℚ) := by
  simp only [zeroVector,repeatWords_ofFn,rowEncode_eq,Pi.zero_apply]
end BinaryEllipsoidInitial
end
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid RationalHeight
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack8
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.state_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open UnaryResources
namespace BinaryWeakSolve
open RationalMatrix

lemma projections_pack (n p s R : ℕ) (rs : List (Row n)) :
    nword (pack n p s R rs)=List.replicate n true ∧
    pword (pack n p s R rs)=List.replicate p true ∧
    sword (pack n p s R rs)=List.replicate s true ∧
    radius (pack n p s R rs)=R.bits ∧ rows (pack n p s R rs)=BinaryRow.rowsEncode rs := by
  simp only [nword,pword,sword,radius,rows,rest₁,rest₂,rest₃,Function.comp_apply,pack,
    extractPrefix_pairBits,discardPrefix_pairBits,and_self]

lemma budgetWord_pack (n p s R : ℕ) (rs : List (Row n)) :
    budgetWord (pack n p s R rs)=List.replicate (iterationBudget n p s) true := by
  obtain ⟨hn,hp,hs,_,_⟩ := projections_pack n p s R rs
  simp only [budgetWord,blocks,twice,hn,hp,hs,←List.replicate_add,copies_replicate,List.length_replicate]
  change RepeatedAppend.copies (n+n) (List.replicate (n*n+(n+n)*(p+s)) true++List.replicate 1 true)=_
  rw [←List.replicate_add,copies_replicate]
  congr 1
  unfold iterationBudget iterationBlocks
  ring

lemma dimBits_pack (n p s R : ℕ) (rs : List (Row n)) : dimBits (pack n p s R rs)=n.bits := by
  rw [dimBits,Function.comp_apply,lengthBits_eq,(projections_pack n p s R rs).1,List.length_replicate]
lemma gridWords_pack (n p s R : ℕ) (rs : List (Row n)) : gridWords (pack n p s R rs)=
    (gridDenominator n (iterationBudget n p s)).bits := by
  simp only [gridWords,cubeWords,dimBits_pack,powerWords,budgetWord_pack,threePower_eq,
    List.length_append,List.length_replicate,List.length_cons,List.length_nil,Nat.zero_add,value_bits]
  congr 1
  unfold gridDenominator
  ring

lemma shapeWords_pack (n p s R : ℕ) (rs : List (Row n)) : shapeWords (pack n p s R rs)=
    RationalMatrix.encode (Ellipsoid.initialState n (R:ℚ)).shape := by
  obtain ⟨hn,_,_,hR,_⟩ := projections_pack n p s R rs
  simp only [shapeWords,radiusSquare,hn,hR,value_bits]
  change BinaryEllipsoidInitial.run (BinaryEllipsoidInitial.pack n ((R:ℚ)*(R:ℚ)))=_
  rw [BinaryEllipsoidInitial.run_pack]
  simp only [Ellipsoid.initialState,pow_two]

lemma centerWords_pack (n p s R : ℕ) (rs : List (Row n)) : centerWords (pack n p s R rs)=
    rowEncode (Ellipsoid.initialState n (R:ℚ)).center := by
  rw [centerWords,(projections_pack n p s R rs).1,BinaryEllipsoidInitial.zeroVector_replicate]
  rfl
lemma advanceInput_pack (n p s R : ℕ) (rs : List (Row n)) : advanceInput (pack n p s R rs)=
    BinaryEllipsoidAdvance.pack (gridDenominator n (iterationBudget n p s)) rs (Ellipsoid.initialState n (R:ℚ)) := by
  simp only [advanceInput,dimBits_pack,gridWords_pack,(projections_pack n p s R rs).2.2.2.2,
    shapeWords_pack,centerWords_pack,BinaryEllipsoidAdvance.pack,BinaryEllipsoidAdvance.stateEncode]
lemma prepared_pack (n p s R : ℕ) (rs : List (Row n)) : prepared (pack n p s R rs)=
    BinaryEllipsoidIteration.pack n (iterationBudget n p s) R rs := by
  simp only [prepared,budgetWord_pack,(projections_pack n p s R rs).2.2.2.1,advanceInput_pack,
    BinaryEllipsoidIteration.pack]
lemma iterated_pack (n p s R : ℕ) (rs : List (Row n)) (hn : 2≤n) (hR : 1≤R) :
    iterated (pack n p s R rs)=BinaryEllipsoidAdvance.pack (gridDenominator n (iterationBudget n p s)) rs
      (Ellipsoid.iterate (gridDenominator n (iterationBudget n p s)) rs (Ellipsoid.initialState n (R:ℚ)) (iterationBudget n p s)) := by
  rw [iterated,Function.comp_apply,prepared_pack,BinaryEllipsoidIteration.run_pack_s238r n _ R rs hn hR]
lemma run_pack (n p s R : ℕ) (rs : List (Row n)) (hn : 2≤n) (hR : 1≤R) :
    run (pack n p s R rs)=WordList.Find.optionEncode ((Ellipsoid.weakSolve rs (R:ℚ) p s).map rowEncode) := by
  rw [run,Function.comp_apply,iterated_pack n p s R rs hn hR]
  simp only [result,BinaryEllipsoidAdvance.found_pack_s238r,BinaryEllipsoidAdvance.center_pack,weakSolve]
  cases he : badRow rs (Ellipsoid.iterate (gridDenominator n (iterationBudget n p s)) rs
      (Ellipsoid.initialState n (R:ℚ)) (iterationBudget n p s)).center with
  | none => simp [WordList.Find.optionEncode]
  | some r => simp [WordList.Find.optionEncode]
end BinaryWeakSolve
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundOp
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.integerDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
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

lemma run_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) (hn : 2≤n) :
    run (pack A b B H)=[integerDecide A b B H] := by
  have hR : 1≤n*(B+1) := by nlinarith
  simp only [run,solved,Function.comp_apply,prepared_pack_s238r,BinaryWeakSolve.run_pack _ _ _ _ _ hn hR,
    Nat.cast_mul,Nat.cast_add,Nat.cast_one,integerDecide]
  cases weakSolve (relaxedRows (gapEpsilon m n H) (boundedRows A b B)) ((n:ℚ)*(B+1))
    (precisionLog m n H) (radiusLog n B) <;> simp [WordList.Find.optionEncode]
end BinaryDecision
end
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
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

namespace BinaryBoundedDecision
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList RationalMatrix

lemma projections_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    nword (pack A b B)=List.replicate n true ∧ mword (pack A b B)=List.replicate m true ∧
    bound (pack A b B)=B.bits ∧
    rows (pack A b B)=BinaryRow.rowsEncode (List.ofFn (fun r=>integerRow (A r) (b r))) := by
  simp only [pack,nword,mword,rest₁,rest₂,bound,rows,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits,and_self]

lemma numAbs_encode (q : ℚ) : numAbs (BinaryRational.encode q)=q.num.natAbs.bits := by
  simp only [numAbs,BinaryRational.encode,extractPrefix_pairBits,Signed.encode,List.tail_cons]
lemma coeffAbs_row {n : ℕ} (a : Fin n → ℤ) (b : ℤ) :
    coeffAbs (BinaryRow.encode (integerRow a b))=NaturalArray.encode (List.ofFn (fun j=>(a j).natAbs)) := by
  simp [coeffAbs,BinaryRow.encode,integerRow,extractPrefix_pairBits,rowEncode_eq,mapWith_ofFn,
    numAbsOp,numAbs_encode,NaturalArray.encode,Function.comp_def]
lemma coeffSum_row {n : ℕ} (a : Fin n → ℤ) (b : ℤ) :
    coeffSum (BinaryRow.encode (integerRow a b))=(∑ j, (a j).natAbs).bits := by
  rw [coeffSum,Function.comp_apply,coeffAbs_row,NaturalArray.sumWords_encode,List.sum_ofFn]
lemma rowHeight_row {n : ℕ} (a : Fin n → ℤ) (b : ℤ) :
    rowHeight (BinaryRow.encode (integerRow a b))=(b.natAbs+∑ j, (a j).natAbs).bits := by
  unfold rowHeight
  rw [coeffSum_row]
  simp [BinaryRow.encode,integerRow,numAbs_encode,discardPrefix_pairBits,value_bits]
lemma rowHeights_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    rowHeights (pack A b B)=NaturalArray.encode (List.ofFn (fun r=>(b r).natAbs+∑ j, (A r j).natAbs)) := by
  simp only [rowHeights,(projections_pack A b B).2.2.2,BinaryRow.rowsEncode,List.map_ofFn,
    Function.comp_def,mapWith_ofFn,rowHeightOp,discardPrefix_pairBits,rowHeight_row,NaturalArray.encode]
lemma height_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    height (pack A b B)=(dataHeight A b B).bits := by
  simp only [height,(projections_pack A b B).2.2.1,heightSum,Function.comp_apply,rowHeights_pack,
    NaturalArray.sumWords_encode,List.sum_ofFn,value_bits,dataHeight]
lemma dataHeight_pad {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    dataHeight (padMatrix A) b B=dataHeight A b B := by
  simp [dataHeight,padMatrix,Fin.sum_univ_add]

lemma padRow_row {n : ℕ} (a : Fin n → ℤ) (b : ℤ) :
    padRow (BinaryRow.encode (integerRow a b))=BinaryRow.encode (integerRow (Fin.append a (fun _ : Fin 2=>0)) b) := by
  have he : (fun j : Fin (n+2) => ((Fin.append a (fun _ : Fin 2=>(0:ℤ)) j : ℤ):ℚ))=Fin.append (fun j=>(a j:ℚ)) (fun _ : Fin 2=>0) := by
    funext j
    refine Fin.addCases (fun i=>?_) (fun i=>?_) j <;> simp
  simp only [padRow,BinaryRow.encode,integerRow,extractPrefix_pairBits,discardPrefix_pairBits,he,rowEncode,
    List.ofFn_fin_append,RationalArray.encode,List.map_append,encode_append]
  rfl
lemma paddedRows_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    paddedRows (pack A b B)=BinaryRow.rowsEncode (List.ofFn (fun r=>integerRow (padMatrix A r) (b r))) := by
  simp only [paddedRows,(projections_pack A b B).2.2.2,BinaryRow.rowsEncode,List.map_ofFn,
    Function.comp_def,mapWith_ofFn,padRowOp,discardPrefix_pairBits,padRow_row,padMatrix]
lemma prepared_pack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    prepared (pack A b B)=BinaryDecision.pack (padMatrix A) b B (dataHeight (padMatrix A) b B) := by
  simp only [prepared,(projections_pack A b B).1,(projections_pack A b B).2.1,
    (projections_pack A b B).2.2.1,height_pack,paddedRows_pack,dataHeight_pad,BinaryDecision.pack]
  congr 2
  simpa using (List.replicate_add n 2 true).symm
lemma run_pack_s238r_oai {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B : ℕ) :
    run (pack A b B)=[boundedIntegerDecide A b B] := by
  rw [run,Function.comp_apply,prepared_pack,BinaryDecision.run_pack _ _ _ _ (by omega)]
  rfl
end BinaryBoundedDecision

open WordOperations
end MetricKMedianRecovery.BitMachine

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack_s238r_oai
