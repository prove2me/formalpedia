-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:52:55.448859+00:00
-- url     : https://prove2.me/submissions/54bb9d62-60a2-43e3-ada5-c0a85da1996f

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L027
import Definitions.Def_Q238L029
import Definitions.Def_Q238L030
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBoundedDecision_run_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryExactSolve_point_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRawOpening_prepared_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_Stored_exactSolve_eq_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_boundedRationalDecide_correct_s238r

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_KindRows
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.EffectiveOpenability

section
open RationalOpenability
variable {D W F : Type*}

lemma mem_subtypeList {m : ℕ} (F : Finset (Fin m)) (f : F) : f∈subtypeList F := by
  exact List.mem_ofFn.mpr ⟨(F.orderIsoOfFin rfl).symm f,by simp⟩

end

open RationalOpenability OpenabilityLinearization

end MetricKMedianRecovery.EffectiveOpenability

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
  rw [run,Function.comp_apply,prepared_pack,BinaryBoundedDecision.run_pack_s238r]
  rfl
end BinaryRationalDecision

open WordOperations
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Rectangular
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid Matrix
namespace BinaryExactSolve
open WordList BinaryRationalDecision RationalMatrix
lemma run_pack {n : ℕ} (rs : List (Row n)) (B : ℕ) :
    run (pack rs B)=resultBits (exactSolve rs B) := by
  rw [run,BinaryRationalDecision.run_pack]
  simp only [List.head?_cons,Option.getD_some,exactSolve]
  split_ifs with h
  · rw [point_pack_s238r rs B ((boundedRationalDecide_correct_s238r rs B).mp h)]
    simp only [h,ite_true, if_true,resultBits]
  · simp [h,resultBits]

end BinaryExactSolve
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace BinaryOpeningActivity
open WordList

lemma optionEncode_nil_iff (o : Option (List Bool)) : Find.optionEncode o=[] ↔ o=none := by
  cases o <;> simp [Find.optionEncode]
end BinaryOpeningActivity
end
open WordOperations BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack10
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryOpeningOracle
open WordOperations BinaryArithmetic RationalLinearFeasibility RationalOpenability
open EffectiveOpenability BinaryExactSolve

lemma run_eq {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) :
    BinaryExactSolve.run (pack distance F W v z lam eta i)=
      resultBits F (storedOpening distance F W v z lam eta i) := by
  unfold pack storedOpening storedForms
  rw [BinaryExactSolve.run_pack,Ellipsoid.Stored.exactSolve_eq_s238r]
  cases h : Ellipsoid.exactSolve
      ((kindRows (List.ofFn (fun j : Fin d=>j)) (subtypeList W) (subtypeList F)).map
        (fun r=>(forms distance F W v z lam eta i r).enumeratedRow (variableEnum d F)))
      ⌈(1+v^2)*z⌉₊ with
  | none=>rfl
  | some y=>simp only [Option.map_some,resultBits,BinaryExactSolve.resultBits,Equiv.symm_apply_apply]

lemma resultBits_eq_nil_iff {m d : ℕ} (F : Finset (Fin m))
    (o : Option (Variables (Fin d) F → ℚ)) : resultBits F o=[] ↔ o=none := by
  cases o <;> simp [resultBits]

end MetricKMedianRecovery.BitMachine.BinaryOpeningOracle

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RowInput
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRawOpening
open WordOperations BinaryArithmetic WordList RationalLinearFeasibility RationalOpenability EffectiveOpenability
open BinaryOpeningPayment BinaryOpeningEnumeration
lemma run_pack {m d : ℕ} (distances : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : run (pack distances F W v z lam eta i)=
      BinaryOpeningOracle.resultBits F (storedOpening distances F W v z lam eta i) := by
  rw [run,Function.comp_apply,prepared_pack_s238r,BinaryOpeningOracle.run_eq]
end MetricKMedianRecovery.BitMachine.BinaryRawOpening

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFirst
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalOpenability
open BinaryOpeningPayment

lemma contains_indices {m : ℕ} (i : Fin m) (fs : List (Fin m)) :
    contains (pairBits (i.val.bits,BinaryOpeningActivity.indices fs))=decide (i∈fs) := by
  simp only [contains,BinaryOpeningActivity.indices,Find.run_encode]
  apply decide_eq_decide.mpr
  simp only [ne_eq,BinaryOpeningActivity.optionEncode_nil_iff,List.find?_eq_none]
  simp only [List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,natEq,
    extractPrefix_pairBits,discardPrefix_pairBits,value_bits,decide_eq_true_eq,← Fin.ext_iff]
  simp only [not_forall,exists_prop,not_not]
  exact ⟨fun ⟨j,hj,he⟩=>he ▸ hj,fun hi=>⟨i,hi,rfl⟩⟩

lemma query_context {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam : ℚ) (i : Fin m) : query (pairBits (context distance F W v z lam,i.val.bits))=
      pack distance F W v z lam 0 i := by
  simp only [query,itemField,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    context,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,pack]

lemma contains_finset {m : ℕ} (i : Fin m) (F : Finset (Fin m)) :
    contains (pairBits (i.val.bits,BinaryOpeningActivity.indices ((subtypeList F).map Subtype.val)))=decide (i∈F) := by
  rw [contains_indices]
  apply decide_eq_decide.mpr
  simp only [List.mem_map]
  exact ⟨fun ⟨j,_,hj⟩=>hj ▸ j.property,fun hi=>⟨⟨i,hi⟩,mem_subtypeList F _,rfl⟩⟩
lemma eligible_context_s238r_oai {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam : ℚ) (i : Fin m) : eligible (pairBits (context distance F W v z lam,i.val.bits))=
      decide (i∈F ∧ i∉W ∧ storedOpening distance F W v z lam 0 i≠none) := by
  unfold eligible
  have ha : answer (pairBits (context distance F W v z lam,i.val.bits))=
      BinaryOpeningOracle.resultBits F (storedOpening distance F W v z lam 0 i) := by
    rw [answer,Function.comp_apply,query_context,BinaryRawOpening.run_pack]
  rw [ha]
  simp only [itemField,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    context,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    contains_finset,decide_eq_true_eq]
  split_ifs <;> simp_all [BinaryOpeningOracle.resultBits_eq_nil_iff]

end MetricKMedianRecovery.BitMachine.BinaryPhaseFirst

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238r_oai
