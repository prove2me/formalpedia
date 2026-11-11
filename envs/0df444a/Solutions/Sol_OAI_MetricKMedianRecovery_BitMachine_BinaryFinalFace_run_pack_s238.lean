-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:39:23.871985+00:00
-- url     : https://prove2.me/submissions/3870d51c-f7eb-4f00-ae06-fc0516ff15fa

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K021
import Definitions.Def_Q238K022
import Definitions.Def_Q238K024
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBoundedDecision_run_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidInitial_indices_replicate_s238

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
  simp only [rowWords,Function.comp_apply,rowInput,extractPrefix_pairBits,pack,indices_replicate_s238,mapWith_ofFn]
  change WordList.encode (List.ofFn (fun j=>entryWords (pairBits (pairBits (pack n q,i.val.bits),j.val.bits))))=_
  simp only [entryWords_pack,rowEncode_eq]

lemma run_pack (n : ℕ) (q : ℚ) : run (pack n q)=
    RationalMatrix.encode (q • (1:Matrix (Fin n) (Fin n) ℚ)) := by
  simp only [run,Function.comp_apply,runInput,pack,extractPrefix_pairBits,indices_replicate_s238,mapWith_ofFn]
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

end NaturalArray
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

section
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryDecision
open WordList RationalMatrix

lemma boundOp_pair {n : ℕ} (b : ℚ) (a : Fin n → ℚ) :
    boundOp (pairBits (BinaryRational.encode b,rowEncode a))=BinaryRow.encode ⟨a,b⟩ := by
  simp only [boundOp,extractPrefix_pairBits,discardPrefix_pairBits,BinaryRow.encode]
end BinaryDecision
end
open WordOperations BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DataHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PolytopeCertificate
open Matrix
open scoped BigOperators
variable {J R V : Type*} [Fintype J] [DecidableEq J] [Fintype R] [Fintype V] [DecidableEq V]

lemma rowNumerator_cast (q : J → ℚ) (i : J) :
    (rowNumerator q i:ℝ)=(rowDenominator q:ℝ)*(q i:ℝ) := by
  have hh : rowDenominator q = (q i).den * ∏ j ∈ Finset.univ.erase i, ((q j).den:ℤ) :=
    (Finset.mul_prod_erase Finset.univ (fun j => ((q j).den:ℤ)) (Finset.mem_univ i)).symm
  rw [hh,Rat.cast_def]
  unfold rowNumerator
  push_cast
  have hn : ((q i).den:ℝ) ≠ 0 := by exact_mod_cast (q i).den_ne_zero
  field_simp

end MetricKMedianRecovery.PolytopeCertificate

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BoundedDecision
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

namespace BinaryClearRow
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid PolytopeCertificate
open WordList RationalMatrix

lemma entries_row {n : ℕ} (r : Row n) :
    entries (BinaryRow.encode r)=RationalArray.encode (r.bound::List.ofFn r.coeff) := by
  simp only [entries,BinaryRow.encode,extractPrefix_pairBits,discardPrefix_pairBits,RationalArray.encode,
    List.map_cons,WordList.encode,rowEncode]
lemma denominators_row {n : ℕ} (r : Row n) : denominators (BinaryRow.encode r)=
    NaturalArray.encode ((r.bound::List.ofFn r.coeff).map Rat.den) := by
  simp only [denominators,entries_row,RationalArray.encode,mapWith_encode,List.map_map,Function.comp_def,
    denOp,discardPrefix_pairBits,BinaryRational.denominator_encode,NaturalArray.encode]
lemma denominator_row {n : ℕ} (r : Row n) : denominator (BinaryRow.encode r)=(rowD r).bits := by
  simp only [denominator,Function.comp_apply,denominators_row,NaturalArray.productWords_encode,
    List.map_cons,List.prod_cons,List.map_ofFn,List.prod_ofFn,rowD,Function.comp_def]
lemma rowD_cast {n : ℕ} (r : Row n) : (rowD r:ℚ)=(rowDenominator (rowEntries r):ℚ) := by
  simp [rowD,rowDenominator,Fintype.prod_option,rowEntries]
lemma rowNumerator_rat {J : Type*} [Fintype J] [DecidableEq J] (q : J → ℚ) (i : J) :
    (rowNumerator q i:ℚ)=(rowDenominator q:ℚ)*q i := by
  apply Rat.cast_injective (α:=ℝ)
  push_cast
  exact rowNumerator_cast q i
lemma scale_coeff {n : ℕ} (r : Row n) (i : Fin n) :
    (rowD r:ℚ)*r.coeff i=(rowNumerator (rowEntries r) (some i):ℚ) := by
  rw [rowD_cast,rowNumerator_rat]
  rfl
lemma scale_bound {n : ℕ} (r : Row n) :
    (rowD r:ℚ)*r.bound=(rowNumerator (rowEntries r) none:ℚ) := by
  rw [rowD_cast,rowNumerator_rat]
  rfl
lemma coeffWords_row {n : ℕ} (r : Row n) : coeffWords (BinaryRow.encode r)=
    rowEncode (fun i=>(rowNumerator (rowEntries r) (some i):ℚ)) := by
  rw [coeffWords,scalar,denominator_row]
  simp only [value_bits,BinaryRow.encode,extractPrefix_pairBits,
    rowEncode_eq,mapWith_ofFn,BinaryRational.mulWords_pair,scale_coeff]
lemma boundWords_row {n : ℕ} (r : Row n) : boundWords (BinaryRow.encode r)=
    BinaryRational.encode (rowNumerator (rowEntries r) none:ℚ) := by
  rw [boundWords,denominator_row]
  simp only [value_bits,BinaryRow.encode,discardPrefix_pairBits,
    BinaryRational.decode_encode,scale_bound]
lemma run_row {n : ℕ} (r : Row n) : run (BinaryRow.encode r)=BinaryRow.encode
    (integerRow (fun i=>rowNumerator (rowEntries r) (some i)) (rowNumerator (rowEntries r) none)) := by
  rw [run,coeffWords_row,boundWords_row]
  rfl
end BinaryClearRow
namespace BinaryRationalDecision
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open WordList

lemma projections_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) :
    first (pack rs B)=List.replicate n true ∧ second (pack rs B)=List.replicate rs.length true ∧
    bound (pack rs B)=B.bits ∧ rows (pack rs B)=BinaryRow.rowsEncode rs := by
  simp only [pack,first,second,rest₁,rest₂,bound,rows,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits,and_self]
lemma clearedRows_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) :
    clearedRows (pack rs B)=BinaryRow.rowsEncode (List.ofFn (fun r=>integerRow (clearedMatrix rs r) (clearedBounds rs r))) := by
  simp only [clearedRows,(projections_pack rs B).2.2.2,BinaryRow.rowsEncode,mapWith_encode,List.map_map,
    Function.comp_def,clearOp,discardPrefix_pairBits,BinaryClearRow.run_row,clearedBounds]
  congr 1
  rw [List.map_ofFn,Function.comp_def]
  exact (List.ofFn_getElem_eq_map rs _).symm
lemma prepared_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) :
    prepared (pack rs B)=BinaryBoundedDecision.pack (clearedMatrix rs) (clearedBounds rs) B := by
  simp only [prepared,(projections_pack rs B).1,(projections_pack rs B).2.1,
    (projections_pack rs B).2.2.1,clearedRows_pack,BinaryBoundedDecision.pack]
lemma run_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) : run (pack rs B)=[boundedRationalDecide rs B] := by
  rw [run,Function.comp_apply,prepared_pack,BinaryBoundedDecision.run_pack_s238]
  rfl
end BinaryRationalDecision

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FaceSelection
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryFace
open WordList
lemma reverse_encode {n : ℕ} (q : Row n) : reverse (BinaryRow.encode q)=BinaryRow.encode (reverseRow q) := by
  simp only [reverse,BinaryRow.encode,extractPrefix_pairBits,discardPrefix_pairBits,
    RationalMatrix.rowEncode_eq,mapWith_ofFn,negEntry,Function.comp_apply,
    BinaryRational.negWords_encode,reverseRow]
lemma reverseRows_encode {n : ℕ} (qs : List (Row n)) :
    reverseRows (BinaryRow.rowsEncode qs)=BinaryRow.rowsEncode (qs.map reverseRow) := by
  simp only [reverseRows,BinaryRow.rowsEncode,mapWith_encode,List.map_map,Function.comp_def,
    reverseOp,discardPrefix_pairBits,reverse_encode]
lemma faceWords_pack {n : ℕ} (rows picked : List (Row n)) (B : ℕ) (q : Row n) :
    faceWords (pairBits (BinaryRationalDecision.pack rows B,pairBits (BinaryRow.encode q,BinaryRow.rowsEncode picked)))=
      BinaryRow.rowsEncode (faceRows rows (q::picked)) := by
  simp only [faceWords,Find.context,Find.item,Find.accum,Function.comp_apply,proposed,
    extractPrefix_pairBits,discardPrefix_pairBits,(BinaryRationalDecision.projections_pack rows B).2.2.2]
  change BinaryRow.rowsEncode rows++BinaryRow.rowsEncode (q::picked)++reverseRows (BinaryRow.rowsEncode (q::picked))=_
  rw [reverseRows_encode]
  simp only [faceRows,BinaryRow.rowsEncode,List.map_append,encode_append]
lemma decisionInput_pack {n : ℕ} (rows picked : List (Row n)) (B : ℕ) (q : Row n) :
    decisionInput (pairBits (BinaryRationalDecision.pack rows B,pairBits (BinaryRow.encode q,BinaryRow.rowsEncode picked)))=
      BinaryRationalDecision.pack (faceRows rows (q::picked)) B := by
  simp only [decisionInput,Find.context,extractPrefix_pairBits,
    (BinaryRationalDecision.projections_pack rows B).1,(BinaryRationalDecision.projections_pack rows B).2.2.1,
    faceWords_pack]
  simp only [BinaryRow.rowsEncode,Count.run_encode,List.length_map,BinaryRationalDecision.pack]
lemma operation_pack {n : ℕ} (rows picked : List (Row n)) (B : ℕ) (q : Row n) :
    Fold.operation op (BinaryRationalDecision.pack rows B) (BinaryRow.rowsEncode picked) (BinaryRow.encode q)=
      BinaryRow.rowsEncode (if boundedRationalDecide (faceRows rows (q::picked)) B then q::picked else picked) := by
  simp only [Fold.operation,op,decision,Function.comp_apply,decisionInput_pack,BinaryRationalDecision.run_pack,
    List.head?_cons,Option.getD_some,proposed,Find.item,Find.accum,extractPrefix_pairBits,discardPrefix_pairBits]
  split <;> rfl
lemma fold_op {n : ℕ} (rows todo picked : List (Row n)) (B : ℕ) :
    (todo.map BinaryRow.encode).foldl (Fold.operation op (BinaryRationalDecision.pack rows B)) (BinaryRow.rowsEncode picked)=
      BinaryRow.rowsEncode (selectFace rows B todo picked) := by
  induction todo generalizing picked with
  | nil => rfl
  | cons q todo ih =>
    rw [List.map_cons,List.foldl_cons,operation_pack]
    unfold selectFace
    split <;> exact ih _
lemma length_selectFace {n : ℕ} (rows todo picked : List (Row n)) (B : ℕ) :
    (BinaryRow.rowsEncode (selectFace rows B todo picked)).length≤
      (BinaryRow.rowsEncode todo).length+(BinaryRow.rowsEncode picked).length := by
  induction todo generalizing picked with
  | nil => simp only [selectFace,BinaryRow.rowsEncode,List.map_nil,encode,List.length_nil,Nat.zero_add,Nat.le_refl]
  | cons q todo ih =>
    unfold selectFace
    split
    · have hh := ih (q::picked)
      simp only [BinaryRow.rowsEncode,List.map_cons,encode,length_cons] at hh ⊢
      omega
    · have hh := ih picked
      simp only [BinaryRow.rowsEncode,List.map_cons,encode,length_cons] at hh ⊢
      omega
lemma run_pack {n : ℕ} (rows todo picked : List (Row n)) (B : ℕ) :
    run (Fold.pack (BinaryRow.rowsEncode todo) (BinaryRationalDecision.pack rows B) (BinaryRow.rowsEncode picked))=
      BinaryRow.rowsEncode (selectFace rows B todo picked) := by
  unfold run
  rw [show BinaryRow.rowsEncode todo=encode (todo.map BinaryRow.encode) from rfl,
    Fold.run_encode op (4*Polynomial.X+4) (BinaryRationalDecision.pack rows B) (BinaryRow.rowsEncode picked)
      (todo.map BinaryRow.encode) ((BinaryRow.rowsEncode todo).length+(BinaryRow.rowsEncode picked).length)]
  · exact fold_op rows todo picked B
  · intro k
    rw [←List.map_take,fold_op]
    have hh := length_selectFace rows (todo.take k) picked B
    have ht := length_encode_take (todo.map BinaryRow.encode) k
    rw [←List.map_take] at ht
    exact hh.trans (Nat.add_le_add_right ht _)
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Fold.length_pack]
    change _≤4*(2*(BinaryRow.rowsEncode todo).length+2*(BinaryRationalDecision.pack rows B).length+(BinaryRow.rowsEncode picked).length+2)+4
    dsimp only [BinaryRow.rowsEncode] at *
    omega
end BinaryFace
namespace BinaryFinalFace
open WordList BinaryRationalDecision
lemma shape_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) (s : Bool) :
    shape s (pack rs B)=RationalMatrix.encode (fun i j : Fin n=>if j=i then (if s then 1 else -1) else 0) := by
  rw [shape,(projections_pack rs B).1]
  change BinaryEllipsoidInitial.run (BinaryEllipsoidInitial.pack n (if s then 1 else -1))=_
  rw [BinaryEllipsoidInitial.run_pack]
  congr 1
  ext i j
  simp only [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
  by_cases h : i=j
  · subst j; simp
  · simp [h,Ne.symm h]
lemma box_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) (s : Bool) :
    box s (pack rs B)=BinaryRow.rowsEncode (List.ofFn (fun i : Fin n=>coordinateRow i (if s then 1 else -1) B)) := by
  simp only [box,(projections_pack rs B).2.2.1,value_bits,shape_pack,RationalMatrix.encode,
    mapWith_ofFn,BinaryDecision.boundOp_pair,BinaryRow.rowsEncode,List.map_ofFn,Function.comp_def,coordinateRow]
lemma allRows_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) :
    allRows (pack rs B)=BinaryRow.rowsEncode (withBox rs B) := by
  simp only [allRows,(projections_pack rs B).2.2.2,box_pack,withBox,boxRows,BinaryRow.rowsEncode,
    List.map_append,encode_append,Bool.false_eq_true,ite_true, if_true,ite_false, if_false]
lemma context_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) : context (pack rs B)=pack (withBox rs B) B := by
  simp only [context,(projections_pack rs B).1,(projections_pack rs B).2.2.1,allRows_pack]
  simp only [BinaryRow.rowsEncode,Count.run_encode,List.length_map,pack]
lemma run_pack_s238_oai {n : ℕ} (rs : List (Row n)) (B : ℕ) : run (pack rs B)=BinaryRow.rowsEncode (finalFace rs B) := by
  rw [run,allRows_pack,context_pack]
  exact BinaryFace.run_pack (withBox rs B) (withBox rs B) [] B
end BinaryFinalFace
end MetricKMedianRecovery.BitMachine

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run_pack_s238_oai
