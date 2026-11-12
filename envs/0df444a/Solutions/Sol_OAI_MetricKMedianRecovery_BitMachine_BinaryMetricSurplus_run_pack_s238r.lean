-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.run_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:17:18.324122+00:00
-- url     : https://prove2.me/submissions/be69fcea-68ed-4fec-8b8e-9a1702ea8da7

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L012
import Definitions.Def_Q238L052
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidInitial_indices_replicate_s238r

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
namespace BinaryRational

lemma natWords_bits (n : ℕ) : natWords n.bits=encode (n:ℚ) := by
  simp only [natWords,value_bits,castIntWords_encode,Int.cast_natCast]
end BinaryRational
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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
variable {n : ℕ}
lemma values_sort (S : Finset (Fin n)) : (values S).sort (·≤·)=(S.sort (·≤·)).map Fin.val := by
  let f : Fin n ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩
  have hh := Finset.map_sort f S (·≤·) (·≤·) (fun a _ b _=>show a≤b↔a.val≤b.val from Iff.rfl)
  simpa only [f,Finset.map_eq_image,values,Function.Embedding.coeFn_mk] using hh.symm
lemma encode_eq (S : Finset (Fin n)) : encode S=WordList.encode ((S.sort (·≤·)).map (fun i=>i.val.bits)) := by
  rw [encode,BinaryNatSet.encode,BinaryNatSet.pack,values_sort,List.map_map]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryFinSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {α : Type*} [LinearOrder α]
lemma map_enum {β : Type*} (S : Finset α) (f : α→β) :
    (S.sort (·≤·)).map f=List.ofFn (fun i=>f (enum S i)) := by rw [←enum_list,List.map_ofFn]; rfl
end MetricKMedianRecovery.SortedIndex
namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
lemma table_enum {n : ℕ} (S : Finset (Fin n)) : table (SortedIndex.enum S)=encode S := by
  unfold table
  rw [←SortedIndex.map_enum S (fun i : Fin n=>i.val.bits),encode_eq]
end MetricKMedianRecovery.BitMachine.BinaryFinSet
namespace MetricKMedianRecovery.BitMachine.BinaryMetricArrays
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n p q : ℕ}
lemma row_pair (δ : Fin n→Fin n→ℚ) (rows : Fin p→Fin n) (cols : Fin q→Fin n) (y : Fin n) :
    row (pairBits (pack δ rows cols,y.val.bits))=RationalMatrix.rowEncode (δ y) := by
  simp only [row,pack,extractPrefix_pairBits,discardPrefix_pairBits,field_encode,List.getElem?_cons_zero,
    Option.getD_some,RationalMatrix.encode,lookup_ofFn]
attribute [local irreducible] BinaryIndexMap.run
lemma column_pair (δ : Fin n→Fin n→ℚ) (rows : Fin p→Fin n) (cols : Fin q→Fin n) (y : Fin n) :
    column (pairBits (pack δ rows cols,y.val.bits))=RationalMatrix.rowEncode (fun j=>δ y (cols j)) := by
  rw [column,row_pair]
  simp only [extractPrefix_pairBits,pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,
    Option.getD_some,RationalMatrix.rowEncode_eq,BinaryFinSet.table,BinaryIndexMap.run,mapWith_ofFn,
    BinaryIndexMap.item,extractPrefix_pairBits,discardPrefix_pairBits,lookup_ofFn]
attribute [local irreducible] mapWith
lemma run_pack (δ : Fin n→Fin n→ℚ) (rows : Fin p→Fin n) (cols : Fin q→Fin n) :
    run (pack δ rows cols)=encode (List.ofFn (fun i=>RationalMatrix.rowEncode (fun j=>δ (rows i) (cols j)))) := by
  unfold run
  rw [show field 1 (pack δ rows cols)=BinaryFinSet.table rows by simp [pack,field_encode]]
  simp only [BinaryFinSet.table,mapWith_ofFn,column_pair]
end MetricKMedianRecovery.BitMachine.BinaryMetricArrays

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricAnchor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricAnchor
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryLocalAnchor.run BinaryProjection.run BinaryMetricArrays.run
variable {n : ℕ}
attribute [local irreducible] WordList.map
attribute [local semireducible] WordList.map
lemma rectInput_pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (r : ℕ) :
    rectInput (pack δ D F r)=BinaryMetricArrays.pack δ id (SortedIndex.enum D) := by
  simp only [rectInput,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryEllipsoidInitial.indices_replicate_s238r,BinaryMetricArrays.pack,BinaryFinSet.table_enum]
  rfl
lemma rectangle_pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (r : ℕ) :
    rectangle (pack δ D F r)=Rectangular.encode (fun i j=>δ i (SortedIndex.enum D j)) := by
  rw [rectangle,Function.comp_apply,rectInput_pack,BinaryMetricArrays.run_pack]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryMetricAnchor

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_MetricSurplus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricSurplus
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
lemma anchorInput_pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (Δ h L : ℕ) :
    anchorInput (pack δ D F Δ h L)=BinaryMetricAnchor.pack δ D F h := by
  simp only [anchorInput,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryMetricAnchor.pack]
lemma rectangle_pack (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (Δ h L : ℕ) :
    rectangle (pack δ D F Δ h L)=Rectangular.encode (fun i j=>δ i (SortedIndex.enum D j)) := by
  rw [rectangle,Function.comp_apply,anchorInput_pack,BinaryMetricAnchor.rectangle_pack]
lemma runInput_pack (δ : Fin n→Fin n→ℕ) (D F : Finset (Fin n)) (Δ h L : ℕ) :
    runInput (pack (fun i j=>(δ i j:ℚ)) D F Δ h L)=BinaryCanonicalSurplus.pack (fun i j=>δ j i) F D Δ h L := by
  rw [runInput,initial,rectangle_pack]
  simp only [total,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryArithmetic.value_bits,BinaryRational.natWords_bits,BinaryFinSet.encode_eq,Count.run_encode,List.length_map,
    Finset.length_sort,BinaryCanonicalSurplus.pack,BinaryInitialAuto.pack]
  rw [←SortedIndex.map_enum D (fun i : Fin n=>i.val.bits)]
lemma run_pack_s238r_oai (v : ℚ) (C : ℕ) (δ : Fin n→Fin n→ℕ) (D F : Finset (Fin n)) (Δ h L : ℕ) :
    run v C (pack (fun i j=>(δ i j:ℚ)) D F Δ h L)=
      BinaryCanonicalSurplus.run v C (BinaryCanonicalSurplus.pack (fun i j=>δ j i) F D Δ h L) := by
  rw [run,Function.comp_apply,runInput_pack]
end MetricKMedianRecovery.BitMachine.BinaryMetricSurplus

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.run_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.run_pack_s238r_oai
