-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryRegular.run_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:14:52.122686+00:00
-- url     : https://prove2.me/submissions/351be4de-be5d-4841-8c0c-8e1a5983fb74

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K043
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryMatch_run_pack_s238
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

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteMachine
open WordOperations WordList RationalLeaves PhaseSequence
open BinaryFiniteContext (labels setBits)
lemma historyBits_append {m : ℕ} (hs gs : List (List (Label (Fin m)))) :
    historyBits (hs++gs)=historyBits hs++historyBits gs := by
  simp only [historyBits,List.map_append,encode_append]
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

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
lemma cuts_prune (C U : List X) :
    (cuts U).map (fun p=>C++p.2.2)=CanonicalMergePath.pruneSuffix C U := by
  induction U generalizing C with
  | nil=>rfl
  | cons a U ih=>
    simp only [cuts,List.map_cons,List.map_map,Function.comp_def,CanonicalMergePath.pruneSuffix,ih]
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
lemma prune_pack {m : ℕ} (C U : List (Label (Fin m))) :
    prune (pairBits (labels C,labels U))=historyBits (CanonicalMergePath.pruneSuffix C U) := by
  simp only [prune,Function.comp_apply,pruneInput,extractPrefix_pairBits,discardPrefix_pairBits,slices_labels_s238,
    Slices.outBits,mapWith_encode,List.map_map,pruneOp,Function.comp_def,extractPrefix_pairBits,discardPrefix_pairBits]
  simp only [(cut_fields _).2.2,←BinaryFiniteContext.labels_append]
  rw [←CanonicalMergeRefinement.cuts_prune]
  simp only [historyBits,List.map_map,Function.comp_def]
end MetricKMedianRecovery.BitMachine.BinarySuffix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchSize
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRegular
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

lemma base_F {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) :
    field 2 (BinaryFiniteContext.pack distance loc F Q v z lam)=setBits F := by
  simp only [BinaryFiniteContext.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma pool_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (key : ℕ) (H J : List (Label (Fin m))) :
    pool (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key H J)=
      labels ((BinaryLabel.orderedSort F).map (copy key)) := by
  simp only [pool,Function.comp_apply,poolInput,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,base_F]
  simp only [setBits,labels,mapWith_encode,List.map_map,Function.comp_def,BinaryLabel.copied_pack]
lemma matchInput_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (key : ℕ) (H J : List (Label (Fin m))) :
    matchInput (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key H J)=
      BinaryMatch.pack (BinaryFiniteContext.pack distance loc F Q v z lam) key F [] J H := by
  simp only [matchInput,context,state0]
  rw [pool_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rfl
lemma run_pack_s238_oai {m d : ℕ} [PseudoMetricSpace (Label (Fin m))]
    (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F B Q : Finset (Label (Fin m))) (v z lam : ℚ) (eta : ℝ) (key : ℕ)
    (hc : CorrectCompletion loc F (v:ℝ) z lam (FiniteLabelContinuation.complete loc (rows distance) F v z lam))
    (hv : (0:ℝ)<v) (hvsmall : (v:ℝ)<1/6) (hz : (0:ℝ)<z) (hlam : (0:ℝ)<lam) (heta : 0≤eta)
    (hQ : Q⊆F∪B) (hdis : Disjoint F B)
    (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) z Q i≤lam)
    (hfresh : ∀ i∈F,copy key i∉F∪B) (hco : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy key i))
    (H J : List (Label (Fin m))) (hHr : ∀ i∈H,i∈F) (hJr : ∀ i∈J,i∈F)
    (hH : Valid loc F B Q v z lam eta H) (hJ : Valid loc F B Q v z lam eta J) :
    run (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key H J)=
      historyBits (regularPath (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) H J) := by
  have hm:=BinaryMatch.run_pack_s238 distance loc F B Q v z lam eta key hc hv hvsmall hz hlam heta hQ hdis hrow hfresh hco
    [] J H (by intro i hi; exact (List.not_mem_nil hi).elim) hJr hHr
    (by simpa only [List.nil_append] using hH.1) (by simpa only [List.nil_append] using hJ)
  simp only [run,prunedInput,matched,Function.comp_apply,matchInput_pack,hm]
  simp only [pack,BinaryMatch.accBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [BinarySuffix.prune_pack,←BinaryFiniteMachine.historyBits_append]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryRegular

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryRegular.run_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryRegular.run_pack_s238_oai
