-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.step_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:07:58.28267+00:00
-- url     : https://prove2.me/submissions/a4862451-f364-4892-8e0f-69fd86da503b

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L039
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_alphabet_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_union_list_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteMachine_completed_pack_s238r

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

end MetricKMedianRecovery.BitMachine.BinaryLabelLookup

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

lemma complete_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    complete (pack distance loc F Q v z lam)=
      labels (FiniteLabelContinuation.complete loc (rows distance) F v z lam Q) := by
  rw [complete,BinaryFiniteContext.alphabet_pack_s238r,completed_pack_s238r]
  rw [labels,BinaryLabelLookup.run_pack]
  rfl

end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
lemma labels_cons {m : ℕ} (x : Label (Fin m)) (xs : List (Label (Fin m))) :
    labels (x::xs)=WordList.cons (BinaryLabel.encode x) (labels xs) := rfl
lemma replaceOpen_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q R : Finset (Label (Fin m))) (v z lam : ℚ) :
    replaceOpen (pairBits (pack distance loc F Q v z lam,setBits R))=pack distance loc F R v z lam := by
  simp only [replaceOpen,extractPrefix_pairBits,discardPrefix_pairBits,pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteMachine
open WordOperations WordList RationalLeaves PhaseSequence
open BinaryFiniteContext (labels setBits)
lemma historyBits_append {m : ℕ} (hs gs : List (List (Label (Fin m)))) :
    historyBits (hs++gs)=historyBits hs++historyBits gs := by
  simp only [historyBits,List.map_append,encode_append]
lemma historyBits_cons {m : ℕ} (H : List (Label (Fin m))) (hs : List (List (Label (Fin m)))) :
    historyBits (H::hs)=WordList.cons (labels H) (historyBits hs) := rfl
lemma historyBits_nil {m : ℕ} : historyBits ([] : List (List (Label (Fin m))))=[] := rfl
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_DeleteFold
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryDelete
open WordOperations WordList RationalLeaves CanonicalDelete
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

lemma tail_labels {m : ℕ} (U : List (Label (Fin m))) : WordList.tail (labels U)=labels U.tail := by
  cases U with
  | nil=>rfl
  | cons u U=>exact WordList.tail_cons _ _

lemma base_open {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    field 3 (BinaryFiniteContext.pack distance loc F Q v z lam)=setBits Q := by
  simp only [BinaryFiniteContext.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

lemma step_pack_s238r_oai {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (C : List (Label (Fin m)))
    (ci a : Label (Fin m)) (s : Acc (Label (Fin m))) :
    step (pairBits (contextBits (BinaryFiniteContext.pack distance loc F Q v z lam) (labels C) (BinaryLabel.encode ci),
      pairBits (BinaryLabel.encode a,accBits s)))=
    accBits (CanonicalDelete.step (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q C ci s a) := by
  simp only [step,vertices,vertex,extras,added,Function.comp_apply,extended,openSet,retained,rest,cf,sf,
    extractPrefix_pairBits,discardPrefix_pairBits,contextBits,accBits,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,tail_labels]
  simp only [base_open]
  rw [←BinaryFiniteContext.labels_cons,←BinaryFiniteContext.labels_append,←BinaryFiniteContext.labels_append]
  rw [BinaryFiniteContext.union_list_pack_s238r,BinaryFiniteContext.replaceOpen_pack,BinaryFiniteMachine.complete_pack]
  simp only [CanonicalDelete.step,BinaryFiniteContext.labels_append,BinaryFiniteContext.labels_cons,
    BinaryFiniteMachine.historyBits_append,BinaryFiniteMachine.historyBits_cons,BinaryFiniteMachine.historyBits_nil]
end MetricKMedianRecovery.BitMachine.BinaryDelete

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.step_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.step_pack_s238r_oai
