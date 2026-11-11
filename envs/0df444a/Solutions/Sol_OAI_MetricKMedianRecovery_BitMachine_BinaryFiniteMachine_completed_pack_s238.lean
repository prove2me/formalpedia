-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completed_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:09:09.953274+00:00
-- url     : https://prove2.me/submissions/31cbc9d3-d6b7-42c8-9172-a9b6827c1367

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K022
import Definitions.Def_Q238K039
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidInitial_indices_replicate_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_alphabet_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_selected_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseTrace_iterate_length_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseTrace_iterate_pack_s238

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
open WordOperations BinaryArithmetic
namespace WordList
lemma map_encode (f : List Bool → List Bool) (ws : List (List Bool)) :
    map f (encode ws)=encode (ws.map f) := by
  simp only [map,mapWith_encode,Function.comp_apply,discardPrefix_pairBits]
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseTrace
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
open BinaryPhaseFinish
attribute [local irreducible] loop loop_computes
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (fuel : ℕ) :
    run (pairBits (List.replicate fuel true,stateBits distance F v lam s))=
      pack distance F v lam (finish distance F v lam fuel s).1 (finish distance F v lam fuel s).2 := by
  have hl : loop (pairBits (List.replicate fuel true,stateBits distance F v lam s))=
      pack distance F v lam (finish distance F v lam fuel s).1 (finish distance F v lam fuel s).2.reverse := by
    simp only [loop,extractPrefix_pairBits,discardPrefix_pairBits]
    change BoundedIteration.run step (pairBits (List.replicate fuel true,pairBits (_,
      pack distance F v lam s [])))=_
    rw [BoundedIteration.run_eq]
    · simp only [List.length_replicate,iterate_pack_s238,List.append_nil]
    · intro j hj
      rw [resource.word_length]
      exact iterate_length_s238 distance F v lam s fuel j (by simpa only [List.length_replicate] using hj)
  simp only [run,hl,pack,extractPrefix_pairBits,discardPrefix_pairBits,WordList.reverse_encode,
    ←List.map_reverse,List.reverse_reverse]
end MetricKMedianRecovery.BitMachine.BinaryPhaseTrace

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Fuel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseRun
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
lemma fuel_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : fuel (stateBits distance F v lam s)=List.replicate F.card true := by
  simp only [fuel,BinaryPhaseAdvance.sf,Function.comp_apply,stateBits,extractPrefix_pairBits,
    BinaryPhaseFirst.context,BinaryOpeningPayment.field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,BinaryOpeningActivity.indices,Count.run_encode,List.length_map,subtypeList,List.length_ofFn]
end MetricKMedianRecovery.BitMachine.BinaryPhaseRun

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_InstructionBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRunTrace
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate

lemma finished_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : finished (stateBits distance F v lam s)=
      BinaryPhaseTrace.pack distance F v lam (finish distance F v lam F.card s).1 (finish distance F v lam F.card s).2 := by
  rw [finished,BinaryPhaseRun.fuel_pack,BinaryPhaseTrace.run_pack]
end MetricKMedianRecovery.BitMachine.BinaryRunTrace

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
  simp only [row,extractPrefix_pairBits,discardPrefix_pairBits,BinaryEllipsoidInitial.indices_replicate_s238,
    mapWith_ofFn,entry_pack,RationalMatrix.rowEncode_eq]

lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (xs : List (Label (Fin m))) :
    run (pairBits (pairBits (Rectangular.encode distance,List.replicate d true),encode (xs.map BinaryLabel.encode)))=
      Rectangular.encode (fun i : Fin xs.length=>rows distance (xs.get i)) := by
  rw [run,mapWith_encode,List.map_map]
  change encode (xs.map (fun x=>row (pairBits (pairBits (Rectangular.encode distance,List.replicate d true),BinaryLabel.encode x))))=_
  simp only [row_pack]
  unfold Rectangular.encode
  congr 1
  exact (List.ofFn_getElem_eq_map xs (RationalMatrix.rowEncode ∘ rows distance)).symm
end MetricKMedianRecovery.BitMachine.BinaryLabelMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FinishPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseCount
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate BinaryOpeningPayment
attribute [local irreducible] WordList.map WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run
lemma contextAt_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F Q : Finset (Fin m))
    (v z lam w : ℚ) : contextAt (pairBits (BinaryPhaseFirst.context distance F Q v z lam,BinaryRational.encode w))=
      BinaryPhaseFirst.context distance F Q v w lam := by
  simp only [contextAt,cf,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    BinaryPhaseFirst.context,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma zeroBudget_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F Q : Finset (Fin m))
    (v z lam : ℚ) : zeroBudget (BinaryPhaseFirst.context distance F Q v z lam)=
      RationalMatrix.rowEncode (fun _ : Fin d=>(0:ℚ)) := by
  simp only [zeroBudget,Function.comp_apply,BinaryOpeningEnumeration.clients,BinaryPhaseFirst.context,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryEllipsoidInitial.indices_replicate_s238,
    map_encode,List.map_ofFn,RationalMatrix.rowEncode_eq]
  rfl
lemma start_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F Q : Finset (Fin m))
    (v z lam w : ℚ) : start (pairBits (BinaryPhaseFirst.context distance F Q v z lam,BinaryRational.encode w))=
      stateBits distance F v lam ⟨Q,w,Vector.replicate d 0⟩ := by
  rw [start,contextAt_pack,extractPrefix_pairBits,zeroBudget_pack]
  simp only [stateBits,Fin.getElem_fin,Vector.getElem_replicate]
end MetricKMedianRecovery.BitMachine.BinaryPhaseCount

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open Classical
open WordOperations WordList BinaryOpeningPayment RationalLeaves
open BinaryLabel (orderedSort)

attribute [local irreducible] BinaryLabelMatrix.run
lemma matrix_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    matrix (pack distance loc F Q v z lam)=Rectangular.encode (FiniteLabelContinuation.rows loc F Q (rows distance)) := by
  rw [matrix,alphabet_pack_s238]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [labels,BinaryLabelMatrix.run_pack]
  rfl

attribute [local irreducible] matrix selected
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    run (pack distance loc F Q v z lam)=BinaryPhaseFirst.context
      (FiniteLabelContinuation.rows loc F Q (rows distance)) (FiniteLabelContinuation.select loc F Q F)
      (FiniteLabelContinuation.select loc F Q Q) v z lam := by
  rw [run,matrix_pack,selected_pack_s238 distance loc F Q Q v z lam 3 (by simp [pack,field_encode]),
    selected_pack_s238 distance loc F Q F v z lam 2 (by simp [pack,field_encode])]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryPhaseFirst.context]
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FiniteMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteMachine
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (pack labels)

lemma initial_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    initial (pack distance loc F Q v z lam)=BinaryPhaseUpdate.stateBits
      (FiniteLabelContinuation.rows loc F Q (rows distance)) (FiniteLabelContinuation.select loc F Q F)
      v lam ⟨FiniteLabelContinuation.select loc F Q Q,z,Vector.replicate d 0⟩ := by
  rw [initial,BinaryFiniteContext.run_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryPhaseCount.start_pack]

lemma completed_pack_s238_oai {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    completed (pack distance loc F Q v z lam)=BinaryOpeningActivity.indices
      (RationalPhase.completion (FiniteLabelContinuation.rows loc F Q (rows distance))
        (FiniteLabelContinuation.select loc F Q F) v z lam (FiniteLabelContinuation.select loc F Q Q)) := by
  simp only [completed,completedTrace,finished,Function.comp_apply,initial_pack,BinaryRunTrace.finished_pack,BinaryPhaseTrace.pack,discardPrefix_pairBits,
    map_encode,BinaryOpeningActivity.indices,RationalPhase.completion,List.map_map,Function.comp_def,
    BinaryPhaseFirst.eventBits,extractPrefix_pairBits]
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completed_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completed_pack_s238_oai
