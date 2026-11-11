-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.cutOp_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:57:31.839599+00:00
-- url     : https://prove2.me/submissions/4a291bd0-0efd-40d4-be2a-d0b246646ef1

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K027
import Definitions.Def_Q238K034
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryJump_view_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySuffix_slices_labels_s238

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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FiniteMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations BinaryArithmetic RationalLeaves
lemma copied_pack {m : ℕ} (key : ℕ) (x : Label (Fin m)) :
    copied (pairBits (key.bits,encode x))=encode (copy key x) := by
  simp only [copied,extractPrefix_pairBits,discardPrefix_pairBits,levelWords_encode,value_bits,parentWords_encode]
  cases x with
  | inl i=>rfl
  | inr c=>simp only [level,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false, if_false,copy,Sum.elim_inr]

end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
lemma labels_cons {m : ℕ} (x : Label (Fin m)) (xs : List (Label (Fin m))) :
    labels (x::xs)=WordList.cons (BinaryLabel.encode x) (labels xs) := rfl
lemma labels_nil {m : ℕ} : labels ([] : List (Label (Fin m)))=[] := rfl

end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

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
-- module Solutions.Q238_KM.KMedianRecovery_Machines_SuffixMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeRefinement
variable {X : Type*}
lemma cuts_grow (C U : List X) (f : X) :
    ((cuts U).map (fun p=>(C++p.2.1::p.2.2)++[f])).reverse=growSuffix C f U := by
  induction U generalizing C with
  | nil=>rfl
  | cons a U ih=>
    simp only [cuts,List.map_cons,List.reverse_cons,List.map_map,Function.comp_def,growSuffix,ih]
end MetricKMedianRecovery.CanonicalMergeRefinement
namespace MetricKMedianRecovery.BitMachine.BinarySuffix
open WordOperations WordList RationalLeaves
open BinaryFiniteContext (labels)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
lemma cut_fields {m : ℕ} (p : List (Label (Fin m)) × Label (Fin m) × List (Label (Fin m))) :
    field 0 (Slices.cutBits BinaryLabel.encode p)=labels p.1 ∧
    field 1 (Slices.cutBits BinaryLabel.encode p)=BinaryLabel.encode p.2.1 ∧
    field 2 (Slices.cutBits BinaryLabel.encode p)=labels p.2.2 := by
  simp [Slices.cutBits,Slices.itemsBits,field_encode,labels]
lemma grow_pack {m : ℕ} (C U : List (Label (Fin m))) (f : Label (Fin m)) :
    grow (pairBits (pairBits (labels C,BinaryLabel.encode f),labels U))=
      historyBits (CanonicalMergeRefinement.growSuffix C f U) := by
  simp only [grow,Function.comp_apply,pruneInput,extractPrefix_pairBits,discardPrefix_pairBits,slices_labels_s238,
    Slices.outBits,mapWith_encode,List.map_map,growOp,Function.comp_def,extractPrefix_pairBits,discardPrefix_pairBits]
  simp only [(cut_fields _).2.1,(cut_fields _).2.2,←BinaryFiniteContext.labels_cons,←BinaryFiniteContext.labels_append]
  rw [show cons (BinaryLabel.encode f) []=labels [f] from rfl]
  simp only [←BinaryFiniteContext.labels_append]
  rw [reverse_encode,←CanonicalMergeRefinement.cuts_grow]
  simp only [historyBits,List.map_reverse,List.map_map,Function.comp_def]
end MetricKMedianRecovery.BitMachine.BinarySuffix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RefineMath
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
lemma expand_pack {m : ℕ} (spare : ℕ) (G : List (Label (Fin m))) (J : Jump (Label (Fin m))) :
    expand (pairBits (encode [spare.bits,labels G],jumpBits J))=historyBits (J.expand (copy spare) G) := by
  cases J with
  | add i=>
    simp only [expand,tagIs,jf,cf,Function.comp_apply,discardPrefix_pairBits,extractPrefix_pairBits,jumpBits,
      field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryArithmetic.value_bits,
      Jump.expand]
    rfl
  | replace C T i=>
    simp only [expand,tagIs,jf,cf,Function.comp_apply,discardPrefix_pairBits,extractPrefix_pairBits,jumpBits,
      field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryArithmetic.value_bits,
      Jump.expand]
    rfl
  | remove C T A i=>
    simp only [expand,tagIs,removeOut,ctSpare,ct,grown,spareWord,jf,cf,Function.comp_apply,
      discardPrefix_pairBits,extractPrefix_pairBits,jumpBits,field_encode,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some,BinaryArithmetic.value_bits,decide_true,ite_true, if_true,BinaryLabel.copied_pack]
    rw [←BinaryFiniteContext.labels_append,BinarySuffix.grow_pack]
    simp only [Jump.expand,removeVertices,historyBits,List.map_cons,List.map_append,List.map_nil,
      encode,encode_append,BinaryFiniteContext.labels_append,BinaryFiniteContext.labels_cons,BinaryFiniteContext.labels_nil]
lemma edge_pack {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key spare : ℕ)
    (H G : List (Label (Fin m))) : edge (encode [ctxBits F R key H G,spare.bits])=
      historyBits (refinedEdge F R (copy key) (copy spare) H G) := by
  have hg : edgeG (encode [ctxBits F R key H G,spare.bits])=labels G := by
    simp only [edgeG,ctxBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  have hv : edgeView (encode [ctxBits F R key H G,spare.bits])=
      Find.optionEncode ((CanonicalMergeRefinement.view F R (copy key) H G).map jumpBits) := by
    simp only [edgeView,Function.comp_apply,field_encode,List.getElem?_cons_zero,Option.getD_some,view_pack_s238]
  simp only [edge,hv,hg,edgeData,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  cases hh : CanonicalMergeRefinement.view F R (copy key) H G with
  | none=>simp only [Option.map_none,Find.optionEncode,ite_true, if_true,refinedEdge,hh]; rfl
  | some J=>
    simp only [Option.map_some,Find.optionEncode,List.cons_ne_nil,ite_false, if_false,List.tail_cons,expand_pack,refinedEdge,hh]
end MetricKMedianRecovery.BitMachine.BinaryJump

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_RefineMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRefine
open WordOperations WordList RationalLeaves CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
lemma cutOp_pack_s238_oai {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key spare : ℕ)
    (p : List (List (Label (Fin m))) × List (Label (Fin m)) × List (List (Label (Fin m)))) :
    cutOp (pairBits (ctxBits F R key spare,Slices.cutBits labels p))=
      historyBits (match p.2.2 with | []=>[] | G::_=>refinedEdge F R (copy key) (copy spare) p.2.1 G) := by
  rcases p with ⟨C,H,T⟩
  simp only [cutOp,cutTail,Slices.cutBits,discardPrefix_pairBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
  cases T with
  | nil=>rfl
  | cons G T=>
    have hn : Slices.itemsBits labels (G::T)≠[] := WordList.cons_ne_nil _ _
    rw [ite_eq_right hn]
    simp only [edgeInput,jumpContext,source,target,cutTail,cf,Function.comp_apply,extractPrefix_pairBits,
      discardPrefix_pairBits,field_encode,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some,Slices.itemsBits_cons,head_cons,ctxBits]
    exact BinaryJump.edge_pack F R key spare H G
end MetricKMedianRecovery.BitMachine.BinaryRefine

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.cutOp_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.cutOp_pack_s238_oai
