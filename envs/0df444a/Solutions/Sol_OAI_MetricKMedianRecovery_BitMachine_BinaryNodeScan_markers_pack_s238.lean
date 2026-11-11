-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan.markers_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:56:54.371054+00:00
-- url     : https://prove2.me/submissions/64e62da0-dbdc-44d4-bf53-dac2b09def54

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K022
import Definitions.Def_Q238K034
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCross_edge_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCross_finalCount_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_WordList_Slices_run_items_s238

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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SliceFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Slices
open WordOperations CanonicalSlices
open BinaryOpeningPayment (field field_computes field_encode)

lemma itemsBits_cons {X : Type*} (enc : X → List Bool) (x : X) (xs : List X) :
    itemsBits enc (x::xs)=cons (enc x) (itemsBits enc xs) := rfl
end MetricKMedianRecovery.BitMachine.WordList.Slices

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RegularChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeCrossing
variable {A B : Type*}

lemma cuts_slots (step : A → A → Option B) (a : A) (T : List A) :
    (CanonicalMergeRefinement.cuts (a::T)).map
      (fun p=>match p.2.2 with | []=>none | b::_=>step p.2.1 b)=slots step a T++[none] := by
  induction T generalizing a with
  | nil=>rfl
  | cons b T ih=>
    rw [CanonicalMergeRefinement.cuts]
    simp only [List.map_cons,List.map_map,Function.comp_def]
    rw [ih]
    rfl
end MetricKMedianRecovery.CanonicalMergeCrossing

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FirstPresent
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCross
open WordOperations WordList RationalLeaves BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] finalCount paid edge
lemma leftCount_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (P R : List (Label (Fin m)) × List (List (Label (Fin m)))) :
    leftCount (pack F Q k P R)=(CanonicalMergeCrossing.finalCount F Q P.1 P.2).bits := by
  rcases P with ⟨H,T⟩
  simp only [leftCount,leftData,leftNode,pack,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,finalCount_pack_s238]
lemma rightCount_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (P R : List (Label (Fin m)) × List (List (Label (Fin m)))) :
    rightCount (pack F Q k P R)=(CanonicalMergeCrossing.finalCount F Q R.1 R.2).bits := by
  rcases R with ⟨G,U⟩
  simp only [rightCount,rightData,rightNode,pack,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,finalCount_pack_s238]
lemma key_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (P R : List (Label (Fin m)) × List (List (Label (Fin m)))) : cf 2 (pack F Q k P R)=k.bits := by
  simp only [cf,pack,Function.comp_apply,extractPrefix_pairBits,ctxBits,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma sandwiched_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (P R : List (Label (Fin m)) × List (List (Label (Fin m)))) :
    sandwiched (pack F Q k P R)=decide (PhaseCountCrossing.Sandwich k
      (CanonicalMergeCrossing.finalCount F Q P.1 P.2) (CanonicalMergeCrossing.finalCount F Q R.1 R.2)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [sandwiched,leftCount_pack,rightCount_pack,key_pack,value_bits,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  unfold PhaseCountCrossing.Sandwich
  rfl
lemma transition_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (P R : List (Label (Fin m)) × List (List (Label (Fin m)))) :
    transition (pack F Q k P R)=FirstPresent.marker resultBits (CanonicalMergeCrossing.transition F Q k P R) := by
  rcases P with ⟨H,T⟩
  rcases R with ⟨G,U⟩
  rw [transition,rightCount_pack,key_pack,sandwiched_pack]
  simp only [value_bits,decide_eq_true_eq,CanonicalMergeCrossing.transition]
  split_ifs <;> simp only [FirstPresent.marker,Option.map_some,Option.map_none,Find.optionEncode,edge_pack_s238]
  simp only [rightNode,pack,Function.comp_apply,discardPrefix_pairBits,successNode,resultBits]
end MetricKMedianRecovery.BitMachine.BinaryCross

namespace MetricKMedianRecovery.BitMachine.BinaryNodeScan
open WordOperations WordList RationalLeaves CanonicalMergeRefinement CanonicalMergeCrossing
open BinaryCross (ctxBits nodeBits resultBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryCross.transition
lemma cutOp_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (p : List (List (Label (Fin m)) × List (List (Label (Fin m)))) ×
      (List (Label (Fin m)) × List (List (Label (Fin m)))) ×
      List (List (Label (Fin m)) × List (List (Label (Fin m))))) :
    cutOp (pairBits (ctxBits F Q k,Slices.cutBits nodeBits p))=
      FirstPresent.marker resultBits (match p.2.2 with | []=>none | b::_=>transition F Q k p.2.1 b) := by
  rcases p with ⟨C,a,T⟩
  simp only [cutOp,suffix,Slices.cutBits,discardPrefix_pairBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
  cases T with
  | nil=>rfl
  | cons b T=>
    have hn : Slices.itemsBits nodeBits (b::T)≠[] := WordList.cons_ne_nil _ _
    rw [ite_eq_right hn]
    simp only [transitionInput,current,suffix,extractPrefix_pairBits,discardPrefix_pairBits,
      field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Slices.itemsBits_cons,head_cons]
    exact BinaryCross.transition_pack F Q k a b
lemma markers_pack_s238_oai {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ) (U : List (List (Label (Fin m))))
    (a : List (Label (Fin m)) × List (List (Label (Fin m))))
    (T : List (List (Label (Fin m)) × List (List (Label (Fin m))))) :
    markers (pack F Q k U (a::T))=encode ((slots (transition F Q k) a T++[none]).map (FirstPresent.marker resultBits)) := by
  simp only [markers,Function.comp_apply,scanInput,pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
  rw [show encode ((a::T).map nodeBits)=Slices.itemsBits nodeBits (a::T) from rfl]
  simp only [Slices.run_items_s238,Slices.outBits,mapWith_encode,List.map_map]
  have hcuts:=cuts_slots (transition F Q k) a T
  simp only [←hcuts,List.map_map,Function.comp_def]
  apply congrArg encode
  apply List.map_congr_left
  rintro ⟨previousNodes,node,remainingNodes⟩ _
  cases remainingNodes with
  | nil=>exact cutOp_pack F Q k (previousNodes,node,[])
  | cons nextNode rest=>exact cutOp_pack F Q k (previousNodes,node,nextNode::rest)
end MetricKMedianRecovery.BitMachine.BinaryNodeScan

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan.markers_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan.markers_pack_s238_oai
