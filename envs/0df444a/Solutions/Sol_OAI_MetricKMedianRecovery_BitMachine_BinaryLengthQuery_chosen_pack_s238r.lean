-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.chosen_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:12:15.587491+00:00
-- url     : https://prove2.me/submissions/b290addb-846b-4e54-a6d4-c3f690f26649

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L043
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidInitial_indices_replicate_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_alphabet_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_selected_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_union_list_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryHistoryRun_run_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseCount_power_pack_s238r

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelMember
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList
lemma lookup_list {α : Type*} (E : α → List Bool) (xs : List α) (i : Fin xs.length) :
    Lookup.run (pairBits (i.val.bits,encode (xs.map E)))=E (xs.get i) := by
  rw [Lookup.run_encode]
  simp only [List.getElem?_map,List.getElem?_eq_getElem i.isLt,Option.map_some,Option.getD_some,List.get_eq_getElem]
end MetricKMedianRecovery.BitMachine.WordList

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabelLookup
open WordOperations WordList RationalLeaves
lemma item_pack {α : Type*} (E : α → List Bool) (xs : List α) (i : Fin xs.length) :
    item (pairBits (encode (xs.map E),i.val.bits))=E (xs.get i) := by
  simp only [item,extractPrefix_pairBits,discardPrefix_pairBits,lookup_list]
lemma run_pack {α : Type*} (E : α → List Bool) (xs : List α) (is : List (Fin xs.length)) :
    run (pairBits (encode (xs.map E),BinaryOpeningActivity.indices is))=
      encode ((is.map xs.get).map E) := by
  simp only [run,BinaryOpeningActivity.indices,mapWith_encode,List.map_map,Function.comp_def,item_pack]

lemma history_pack {α : Type*} (E : α → List Bool) (xs : List α) (hs : List (List (Fin xs.length))) :
    history (pairBits (encode (xs.map E),BinaryHistoryRun.historyBits hs))=
      encode ((hs.map (List.map xs.get)).map (fun H=>encode (H.map E))) := by
  simp only [history,BinaryHistoryRun.historyBits,mapWith_encode,List.map_map,Function.comp_def,run_pack]
end MetricKMedianRecovery.BitMachine.BinaryLabelLookup

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
  WordList.Fold.run BinaryPhaseRun.run
lemma contextAt_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F Q : Finset (Fin m))
    (v z lam w : ℚ) : contextAt (pairBits (BinaryPhaseFirst.context distance F Q v z lam,BinaryRational.encode w))=
      BinaryPhaseFirst.context distance F Q v w lam := by
  simp only [contextAt,cf,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    BinaryPhaseFirst.context,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma zeroBudget_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F Q : Finset (Fin m))
    (v z lam : ℚ) : zeroBudget (BinaryPhaseFirst.context distance F Q v z lam)=
      RationalMatrix.rowEncode (fun _ : Fin d=>(0:ℚ)) := by
  simp only [zeroBudget,Function.comp_apply,BinaryOpeningEnumeration.clients,BinaryPhaseFirst.context,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryEllipsoidInitial.indices_replicate_s238r,
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
  rw [matrix,alphabet_pack_s238r]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [labels,BinaryLabelMatrix.run_pack]
  rfl

attribute [local irreducible] matrix selected
lemma run_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    run (pack distance loc F Q v z lam)=BinaryPhaseFirst.context
      (FiniteLabelContinuation.rows loc F Q (rows distance)) (FiniteLabelContinuation.select loc F Q F)
      (FiniteLabelContinuation.select loc F Q Q) v z lam := by
  rw [run,matrix_pack,selected_pack_s238r distance loc F Q Q v z lam 3 (by simp [pack,field_encode]),
    selected_pack_s238r distance loc F Q F v z lam 2 (by simp [pack,field_encode])]
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

lemma start_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (q n : ℕ) :
    start (pairBits (List.replicate n true,pairBits (List.replicate q true,pack distance loc F Q v z lam)))=
      BinaryPhaseUpdate.stateBits (FiniteLabelContinuation.rows loc F Q (rows distance))
        (FiniteLabelContinuation.select loc F Q F) v lam
        ⟨FiniteLabelContinuation.select loc F Q Q,(1+v^2)^q,Vector.replicate d 0⟩ := by
  simp only [start,phase,data,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,BinaryFiniteContext.run_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryPhaseCount.power_pack_s238r,BinaryPhaseCount.start_pack]

lemma continuation_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (q n : ℕ) :
    continuation (pairBits (List.replicate n true,pairBits (List.replicate q true,pack distance loc F Q v z lam)))=
      historyBits (FiniteLabelContinuation.continuation loc (rows distance) F v lam q n Q) := by
  simp only [continuation,history,data,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    BinaryFiniteContext.alphabet_pack_s238r,start_pack,BinaryHistoryRun.run_pack_s238r,BinaryHistoryRun.pack]
  rw [labels,BinaryLabelLookup.history_pack]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
lemma labels_cons {m : ℕ} (x : Label (Fin m)) (xs : List (Label (Fin m))) :
    labels (x::xs)=WordList.cons (BinaryLabel.encode x) (labels xs) := rfl
lemma labels_nil {m : ℕ} : labels ([] : List (Label (Fin m)))=[] := rfl

lemma replaceOpen_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q R : Finset (Label (Fin m))) (v z lam : ℚ) :
    replaceOpen (pairBits (pack distance loc F Q v z lam,setBits R))=pack distance loc F R v z lam := by
  simp only [replaceOpen,extractPrefix_pairBits,discardPrefix_pairBits,pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LengthQuery
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLengthQuery
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryFiniteMachine.continuation

lemma newLeaf_pack {m : ℕ} (base : List Bool) (n q key : ℕ) (root : Label (Fin m)) (b s : ℚ)
    (T U : List (List (Label (Fin m)))) :
    newLeaf (pairBits (ctxBits base n q key root b T U,BinaryRational.encode s))=
      BinaryLabel.encode (leaf key (parent root) s) := by
  simp only [newLeaf,cf,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,ctxBits,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,
    BinaryLabel.parentWords_encode]
  rfl
lemma opened_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (i : Label (Fin m)) (b s : ℚ)
    (T U : List (List (Label (Fin m)))) :
    opened (pairBits (ctxBits (BinaryFiniteContext.pack distance loc F Q v z lam) n q key i b T U,BinaryRational.encode s))=
      setBits (insert (leaf key (parent i) s) Q) := by
  unfold opened
  rw [newLeaf_pack]
  simp only [cf,Function.comp_apply,extractPrefix_pairBits,ctxBits,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFiniteContext.pack]
  rw [←BinaryFiniteContext.labels_nil,←BinaryFiniteContext.labels_cons,BinaryFiniteContext.union_list_pack_s238r]
  simp only [List.toFinset_cons,List.toFinset_nil,Finset.union_insert,Finset.union_empty]
lemma interior_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (i : Label (Fin m)) (b s : ℚ)
    (T U : List (List (Label (Fin m)))) :
    interior (pairBits (ctxBits (BinaryFiniteContext.pack distance loc F Q v z lam) n q key i b T U,BinaryRational.encode s))=
      historyBits (FiniteLabelContinuation.continuation loc (rows distance) F v lam q n (insert (leaf key (parent i) s) Q)) := by
  simp only [interior,base,opened_pack]
  simp only [cf,Function.comp_apply,extractPrefix_pairBits,ctxBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,BinaryFiniteContext.replaceOpen_pack,BinaryFiniteMachine.continuation_pack]
lemma chosen_pack_s238r_oai {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (i : Label (Fin m)) (b s : ℚ)
    (T U : List (List (Label (Fin m)))) :
    chosen (pairBits (ctxBits (BinaryFiniteContext.pack distance loc F Q v z lam) n q key i b T U,BinaryRational.encode s))=
      historyBits (CanonicalLengthSearch.chosen
        (fun s=>FiniteLabelContinuation.continuation loc (rows distance) F v lam q n (insert (leaf key (parent i) s) Q)) T U b s) := by
  unfold chosen
  rw [interior_pack]
  simp only [isZero,isUpper,cf,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,
    ctxBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryRational.decode_encode,
    decide_eq_true_eq,CanonicalLengthSearch.chosen]
  split_ifs <;> rfl
end MetricKMedianRecovery.BitMachine.BinaryLengthQuery

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.chosen_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.chosen_pack_s238r_oai
