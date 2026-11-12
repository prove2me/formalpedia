-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryLength.view_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:54:40.548113+00:00
-- url     : https://prove2.me/submissions/c39a17ba-e228-4760-9f88-53c31555da1a

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L029
import Definitions.Def_Q238L030
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidInitial_indices_replicate_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySuffix_slices_labels_s238r

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace MetricTable
open WordList

lemma get_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (f : Fin m) (j : Fin d) :
    get (pairBits (pairBits (Rectangular.encode distance,f.val.bits),j.val.bits))=
      BinaryRational.encode (distance f j) := by
  simp only [get,getRow,context,row,col,Function.comp_apply,
    extractPrefix_pairBits,discardPrefix_pairBits,Rectangular.encode,lookup_ofFn,
    RationalMatrix.rowEncode_eq]
end MetricTable
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
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [LinearOrder V]

omit [LinearOrder V] in
lemma rows_height {d : ℕ} (distance : V → Fin d → ℚ) (x : Label V) (j : Fin d) :
    rows distance x j=distance (parent x) j+max (rationalHeight x) 0 := by
  cases x <;> simp [rows,parent,rationalHeight]
end MetricKMedianRecovery.RationalLeaves

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations BinaryArithmetic RationalLeaves

attribute [local irreducible] MetricTable.get
lemma row_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (x : Label (Fin m)) (j : Fin d) :
    row (pairBits (pairBits (Rectangular.encode distance,encode x),j.val.bits))=
      BinaryRational.encode (rows distance x j) := by
  simp only [row,rawRow,table,label,col,Function.comp_apply,extractPrefix_pairBits,
    discardPrefix_pairBits,parentWords_encode,heightWords_encode,MetricTable.get_pack,BinaryRational.decode_encode,rows_height]
end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryLabelMatrix
open WordOperations WordList RationalLeaves
attribute [local irreducible] mapWith

lemma entry_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (x : Label (Fin m)) (j : Fin d) :
    entry (pairBits (pairBits (pairBits (Rectangular.encode distance,List.replicate d true),BinaryLabel.encode x),j.val.bits))=
      BinaryRational.encode (rows distance x j) := by
  simp only [entry,table,item,col,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,BinaryLabel.row_pack]

lemma row_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (x : Label (Fin m)) :
    row (pairBits (pairBits (Rectangular.encode distance,List.replicate d true),BinaryLabel.encode x))=
      RationalMatrix.rowEncode (rows distance x) := by
  simp only [row,extractPrefix_pairBits,discardPrefix_pairBits,BinaryEllipsoidInitial.indices_replicate_s238r,
    mapWith_ofFn,entry_pack,RationalMatrix.rowEncode_eq]

end MetricKMedianRecovery.BitMachine.BinaryLabelMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelMember
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations BinaryArithmetic WordList RationalLeaves

lemma fields_injective {m : ℕ} (a b : Label (Fin m)) :
    level a=level b ∧ (parent a).val=(parent b).val ∧ rationalHeight a=rationalHeight b ↔ a=b := by
  cases a <;> cases b <;> simp [level,parent,root,rationalHeight,Fin.ext_iff,Prod.ext_iff]
lemma eq_pair {m : ℕ} (a b : Label (Fin m)) : eq (pairBits (encode a,encode b))=decide (a=b) := by
  simp only [eq,extractPrefix_pairBits,discardPrefix_pairBits,levelWords_encode,parentWords_encode,
    heightWords_encode,value_bits,BinaryRational.decode_encode,←Bool.decide_and,fields_injective]

lemma contains_encode {m : ℕ} (a : Label (Fin m)) (xs : List (Label (Fin m))) :
    contains (pairBits (encode a,WordList.encode (xs.map encode)))=by classical exact decide (a∈xs) := by
  classical
  simp only [contains,Find.run_encode]
  apply decide_eq_decide.mpr
  simp only [ne_eq,BinaryOpeningActivity.optionEncode_nil_iff,List.find?_eq_none]
  simp only [List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂,eq_pair,decide_eq_true_eq]
  simp only [not_forall,exists_prop,not_not]
  exact ⟨fun ⟨b,hb,he⟩=>he ▸ hb,fun ha=>⟨a,ha,rfl⟩⟩

theorem encode_injective {m : ℕ} : Function.Injective (@encode m) := by
  intro a b h
  have hq:=eq_pair a b
  rw [h,eq_pair b b] at hq
  exact of_decide_eq_true (by simpa only [decide_true] using hq.symm)

end MetricKMedianRecovery.BitMachine.BinaryLabel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FiniteMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_encode)
lemma labels_cons {m : ℕ} (x : Label (Fin m)) (xs : List (Label (Fin m))) :
    labels (x::xs)=WordList.cons (BinaryLabel.encode x) (labels xs) := rfl
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordEq
lemma eq_pair (xs ys : List Bool) : eq (pairBits (xs,ys))=decide (xs=ys) := by
  simp only [eq,extractPrefix_pairBits,discardPrefix_pairBits]
end WordEq
namespace WordList
lemma encode_injective : Function.Injective encode := by
  intro xs
  induction xs with
  | nil=>
    intro ys he
    cases ys with
    | nil=>rfl
    | cons y ys=>exact (cons_ne_nil y (encode ys) he.symm).elim
  | cons x xs ih=>
    intro ys he
    cases ys with
    | nil=>exact (cons_ne_nil x (encode xs) he).elim
    | cons y ys=>
      have hh:=congrArg head he
      have ht:=congrArg tail he
      simp only [encode,head_cons] at hh
      simp only [encode,tail_cons] at ht
      exact congrArg₂ List.cons hh (ih ht)
end WordList
end MetricKMedianRecovery.BitMachine

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves
lemma labels_injective {m : ℕ} : Function.Injective (@labels m) := by
  intro A B h
  apply List.map_injective_iff.mpr BinaryLabel.encode_injective
  exact WordList.encode_injective h
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext
namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations WordList RationalLeaves
lemma contains_setBits {m : ℕ} (a : Label (Fin m)) (F : Finset (Label (Fin m))) :
    contains (pairBits (encode a,BinaryFiniteContext.setBits F))=decide (a∈F) := by
  simp only [BinaryFiniteContext.setBits,BinaryFiniteContext.labels,contains_encode,orderedSort,Finset.mem_sort]
end MetricKMedianRecovery.BitMachine.BinaryLabel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LengthEncode
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.RationalMatrix
lemma rowEncode_injective {d : ℕ} : Function.Injective (@rowEncode d) := by
  intro a b h
  simp only [rowEncode_eq] at h
  have hf := List.ofFn_injective (WordList.encode_injective h)
  funext j
  have hd := congrArg BinaryRational.decode (congrFun hf j)
  simpa only [BinaryRational.decode_encode] using hd
end MetricKMedianRecovery.BitMachine.RationalMatrix
namespace MetricKMedianRecovery.BitMachine.BinaryLength
open WordOperations WordList RationalLeaves CanonicalLengthView BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] BinaryLabelMatrix.row
lemma accepts_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Label (Fin m)))
    (R H G : List (Label (Fin m))) (J : Plan (Label (Fin m))) :
    accepts (pairBits (ctxBits distance F R H G,planBits J))=
      decide (CanonicalLengthView.accepts (rows distance) F H G J) := by
  apply Bool.eq_iff_iff.mpr
  cases J <;> simp only [accepts,rootIn,source,target,extra,isFree,freeOut,sameRow,row,cf,pf,
    Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,ctxBits,planBits,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,
    BinaryLabel.contains_setBits,BinaryLabelMatrix.row_pack,WordEq.eq_pair]
  · rename_i i f
    simp only [decide_true,ite_true, if_true,decide_eq_true_eq,eq_self,Bool.and_eq_true,true_and,
      Bool.not_eq_true',decide_eq_false_iff_not]
    rw [show cons (BinaryLabel.encode f) []=labels [f] from rfl, ←BinaryFiniteContext.labels_append]
    simp only [BinaryFiniteContext.labels_injective.eq_iff,RationalMatrix.rowEncode_injective.eq_iff,
      CanonicalLengthView.accepts]
    rw [funext_iff]
    tauto
  · rename_i C T i
    simp only [Nat.one_ne_zero,decide_false,Bool.false_eq_true,ite_false, if_false,decide_eq_true_eq,
      Bool.and_eq_true,and_true]
    rw [←BinaryFiniteContext.labels_cons,←BinaryFiniteContext.labels_append,←BinaryFiniteContext.labels_append]
    simp only [BinaryFiniteContext.labels_injective.eq_iff,CanonicalLengthView.accepts]
end MetricKMedianRecovery.BitMachine.BinaryLength

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SuffixMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySuffix
open WordOperations WordList RationalLeaves
open BinaryFiniteContext (labels)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_encode)
lemma cut_fields {m : ℕ} (p : List (Label (Fin m)) × Label (Fin m) × List (Label (Fin m))) :
    field 0 (Slices.cutBits BinaryLabel.encode p)=labels p.1 ∧
    field 1 (Slices.cutBits BinaryLabel.encode p)=BinaryLabel.encode p.2.1 ∧
    field 2 (Slices.cutBits BinaryLabel.encode p)=labels p.2.2 := by
  simp [Slices.cutBits,Slices.itemsBits,field_encode,labels]
end MetricKMedianRecovery.BitMachine.BinarySuffix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthCandidates
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLength
open WordOperations WordList RationalLeaves CanonicalLengthView BinaryArithmetic CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] WordList.mapWith
lemma frees_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Label (Fin m)))
    (R H G : List (Label (Fin m))) : frees (ctxBits distance F R H G)=
      encode ((R.flatMap (fun i=>G.map (Plan.free i))).map planBits) := by
  simp only [frees,ctxBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    labels,crossWith_encode,List.flatMap_map,List.map_map,Function.comp_def,List.map_flatMap,
    freeOp,extractPrefix_pairBits,discardPrefix_pairBits,planBits]
lemma paids_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Label (Fin m)))
    (R H G : List (Label (Fin m))) : paids (ctxBits distance F R H G)=
      encode (((cuts H).map (fun p=>Plan.paid p.1 p.2.2 p.2.1)).map planBits) := by
  have hh : field 2 (ctxBits distance F R H G)=labels H := by
    simp only [ctxBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  simp only [paids,hh,BinarySuffix.slices_labels_s238r,Slices.outBits,mapWith_encode,List.map_map,
    Function.comp_def,paidOp,pf,discardPrefix_pairBits,
    (BinarySuffix.cut_fields _).1,(BinarySuffix.cut_fields _).2.1,(BinarySuffix.cut_fields _).2.2,planBits]
lemma candidates_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Label (Fin m)))
    (R H G : List (Label (Fin m))) : candidates (ctxBits distance F R H G)=
      encode ((CanonicalLengthView.candidates R H G).map planBits) := by
  simp only [candidates,frees_pack,paids_pack,CanonicalLengthView.candidates,List.map_append,encode_append]
lemma view_pack_s238r_oai {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Label (Fin m)))
    (R H G : List (Label (Fin m))) : view (ctxBits distance F R H G)=
      Find.optionEncode ((CanonicalLengthView.view (rows distance) F R H G).map planBits) := by
  simp only [view,candidates_pack,Find.run_encode,List.find?_map,Function.comp_def,accepts_pack,CanonicalLengthView.view]
end MetricKMedianRecovery.BitMachine.BinaryLength

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryLength.view_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryLength.view_pack_s238r_oai
