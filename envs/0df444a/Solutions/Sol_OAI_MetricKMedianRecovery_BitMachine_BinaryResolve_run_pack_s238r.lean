-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryResolve.run_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:12:48.762738+00:00
-- url     : https://prove2.me/submissions/4db33e66-d123-4a74-b0f1-969f0aae9576

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L043
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_union_list_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryLength_view_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySensitive_run_pack_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [LinearOrder V]

lemma label_lt (a b : Label V) : @LT.lt _ (labelLinearOrder.toLT) a b ↔
    level a<level b ∨ level a=level b ∧
      (parent a<parent b ∨ parent a=parent b ∧ rationalHeight a < rationalHeight b) := by
  change Sum.Lex (fun a b : V=>a<b)
    (fun a b : ℕ × V × ℚ=>Prod.Lex (·<·) (Prod.Lex (·<·) (·<·)) a b) a b ↔ _
  cases a with
  | inl a=>
    cases b with
    | inl b=>simp [Sum.lex_inl_inl,level,parent,rationalHeight]
    | inr b=>simp [Sum.Lex.sep,level]
  | inr a=>
    cases b with
    | inl b=>simp [Sum.lex_inr_inl,level]
    | inr b=>simp [Sum.lex_inr_inr,Prod.lex_iff,level,parent,root,rationalHeight]

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_CoupledEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
attribute [local irreducible] BinaryCorrection.mapHistory
lemma historyBits_append {m : ℕ} (P T : List (List (Label (Fin m)))) : historyBits (P++T)=historyBits P++historyBits T := by
  simp only [historyBits,List.map_append,encode_append]
lemma historyBits_cons {m : ℕ} (H : List (Label (Fin m))) (T : List (List (Label (Fin m)))) :
    historyBits (H::T)=cons (labels H) (historyBits T) := rfl
lemma finish_pack {m : ℕ} (B : Finset (Label (Fin m))) (lam : ℚ) (P T : List (List (Label (Fin m)))) :
    finish (encode [setBits B,BinaryRational.encode lam,historyBits P,historyBits T])=
      outputBits (CanonicalCoupledMerge.finish B lam P T) := by
  simp only [finish,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    outputBits,CanonicalCoupledMerge.finish,historyBits_append]
lemma same_pack {m : ℕ} (B : Finset (Label (Fin m))) (lam : ℚ) (P T U : List (List (Label (Fin m)))) :
    same (encode [setBits B,BinaryRational.encode lam,historyBits P,historyBits T,historyBits U])=
      stateBits (sameState B lam P T U) := by
  simp only [same,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    stateBits,sameState,BinaryCorrection.encode]
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CoupledPrimitives
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
lemma makeLeaf_pack {m : ℕ} (key : ℕ) (i : Label (Fin m)) (s : ℚ) :
    makeLeaf (WordList.encode [key.bits,encode i,BinaryRational.encode s])=encode (leaf key (parent i) s) := by
  simp only [makeLeaf,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,parentWords_encode]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
lemma endLeaf_pack {m : ℕ} (B : Finset (Label (Fin m))) (P : List (List (Label (Fin m)))) (lam : ℚ)
    (key : ℕ) (i : Label (Fin m)) (C : List (Label (Fin m))) (l u : ℚ) (T U : List (List (Label (Fin m)))) :
    endLeaf 6 (leafPack B P lam key i C l u T U)=BinaryLabel.encode (leaf key (parent i) l) ∧
    endLeaf 7 (leafPack B P lam key i C l u T U)=BinaryLabel.encode (leaf key (parent i) u) := by
  simp only [endLeaf,leafPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryLabel.makeLeaf_pack,and_self]
lemma leafResult_pack {m : ℕ} (B : Finset (Label (Fin m))) (P : List (List (Label (Fin m)))) (lam : ℚ)
    (key : ℕ) (i : Label (Fin m)) (C : List (Label (Fin m))) (l u : ℚ) (T U : List (List (Label (Fin m)))) :
    leafResult (leafPack B P lam key i C l u T U)=stateBits (leafState B P lam key (parent i) C l u T U) := by
  obtain ⟨hl,hu⟩:=endLeaf_pack B P lam key i C l u T U
  unfold leafResult leafBank leafPrefix
  rw [hl,hu]
  simp only [leafPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  change encode [BinaryFiniteContext.union (pairBits (setBits B,labels [leaf key (parent i) u])),_,_,_,_,_,_]=_
  rw [BinaryFiniteContext.union_list_pack_s238r]
  simp only [List.toFinset_cons,List.toFinset_nil,Finset.union_insert,Finset.union_empty,
    stateBits,leafState,historyBits_append,historyBits_cons,BinaryFiniteContext.labels_append,
    BinaryCorrection.encode]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PlanResult
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPlanResult
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

lemma run_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q B : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (H : List (Label (Fin m))) (T U P : List (List (Label (Fin m)))) (J : Plan (Label (Fin m)))
    (R : CanonicalLengthSearch.Result (Label (Fin m))) :
    run (pack (BinarySensitive.pack (BinaryFiniteContext.pack distance loc F Q v z lam) n q key b k N H T U J) B P R)=
      BinaryCoupled.outcomeBits (match R with
      | .success s W=>.inl (CanonicalCoupledMerge.finish (insert (leaf key (parent J.root) s) B) lam (P++[J.common H++[leaf key (parent J.root) s]]) W)
      | .bracket l u A Z=>.inr (leafState B P lam key (parent J.root) (J.common H) l u A Z)) := by
  have hl:=leafInput_pack distance loc F Q B v z lam n q key b k N H T U P J R
  unfold run
  cases R with
  | success s W=>
    simp only [success,rf,Function.comp_apply,pack,BinaryLengthSearch.resultBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,decide_true,ite_true, if_true] at *
    unfold finishInput
    rw [hl]
    simp only [price,sf,rf,Function.comp_apply,BinarySensitive.pack,BinaryFiniteContext.pack,
      field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
    have hu:=(BinaryCoupled.endLeaf_pack B P lam key J.root (J.common H) s s W []).2
    unfold BinaryCoupled.leafBank BinaryCoupled.leafPrefix
    rw [hu]
    simp only [BinaryCoupled.leafPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
    change pairBits ([],BinaryCoupled.finish (encode [BinaryFiniteContext.union (pairBits (setBits B,labels [leaf key (parent J.root) s])),_,_,_]))=_
    rw [BinaryFiniteContext.union_list_pack_s238r]
    simp only [List.toFinset_cons,List.toFinset_nil,Finset.union_insert,Finset.union_empty]
    rw [show historyBits P++cons (labels (J.common H)++cons (BinaryLabel.encode (leaf key (parent J.root) s)) []) []=
      historyBits (P++[J.common H++[leaf key (parent J.root) s]]) by
      rw [BinaryCoupled.historyBits_append,BinaryCoupled.historyBits_cons,BinaryFiniteContext.labels_append]; rfl]
    rw [BinaryCoupled.finish_pack]
    rfl
  | bracket l u A Z=>
    simp only [success,rf,Function.comp_apply,pack,BinaryLengthSearch.resultBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,one_ne_zero,decide_false,Bool.false_eq_true,ite_false, if_false] at *
    rw [hl,BinaryCoupled.leafResult_pack]
    rfl
end MetricKMedianRecovery.BitMachine.BinaryPlanResult

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
lemma original_order {m : ℕ} (a b : Fin m) : (a≤b) ↔ (@LE.le _ (labelLinearOrder.toLE) (original a) (original b)) := by
  rw [←not_lt,←not_lt,label_lt]
  simp [original,level,parent,rationalHeight]
lemma originalSort {m : ℕ} (F : Finset (Fin m)) :
    (F.sort (·≤·)).map original=BinaryLabel.orderedSort (F.image original) := by
  let f : Fin m↪Label (Fin m):=original
  have h:=Finset.map_sort f F (·≤·) (@LE.le _ (labelLinearOrder.toLE)) (fun a _ b _=>original_order a b)
  simpa only [f,Finset.map_eq_image,BinaryLabel.orderedSort] using h
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_ResolveMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryResolve
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
lemma view_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m))
    (Q B : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (P : List (List (Label (Fin m)))) (H G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) :
    view (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q v z lam) n q key b k N B P (.sensitive H G T U))=
      Find.optionEncode ((CanonicalLengthView.view (rows distance) (F.image original) ((F.sort (·≤·)).map original) H G).map BinaryLength.planBits) := by
  unfold view viewInput
  simp only [BinaryResolve.H,BinaryResolve.G,bf,rf,Function.comp_apply,pack,BinaryCross.resultBits,BinaryCross.nodeBits,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,extractPrefix_pairBits,
    BinaryFiniteContext.pack]
  change BinaryLength.view (BinaryLength.ctxBits distance (F.image original) (BinaryLabel.orderedSort (F.image original)) H G)=_
  rw [←BinaryFiniteContext.originalSort]
  exact BinaryLength.view_pack_s238r ..
lemma run_pack_s238r_oai {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m))
    (B : Finset (Label (Fin m))) (v z lam M : ℚ) (n q key N precision k : ℕ)
    (P : List (List (Label (Fin m)))) (R : CanonicalMergeCrossing.Result (Label (Fin m))) :
    run (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) (PhaseHistoryTransfer.after ∅ P) v z lam)
      n q key (20*N*M) k precision B P R)=
      BinaryCoupled.outcomeBits (CanonicalCoupledMerge.resolve loc distance F v M N precision q n k key B lam P R) := by
  let base:=BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) (PhaseHistoryTransfer.after ∅ P) v z lam
  change run (pack base n q key (20*N*M) k precision B P R)=_
  cases R with
  | success H T=>
    simp only [run,rf,Function.comp_apply,pack,BinaryCross.resultBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,ite_true, if_true]
    simp only [finishInput,prefixH,bf,rf,BinaryResolve.H,BinaryResolve.T,Function.comp_apply,base,BinaryFiniteContext.pack,
      BinaryCross.nodeBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,extractPrefix_pairBits,discardPrefix_pairBits]
    rw [show historyBits P++cons (labels H) []=historyBits (P++[H]) by rw [BinaryCoupled.historyBits_append,BinaryCoupled.historyBits_cons]; rfl]
    rw [BinaryCoupled.finish_pack]
    rfl
  | common H T U=>
    simp only [run,rf,Function.comp_apply,pack,BinaryCross.resultBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,one_ne_zero,ite_false, if_false,ite_true, if_true]
    simp only [sameInput,prefixH,bf,rf,BinaryResolve.H,BinaryResolve.T,Function.comp_apply,base,BinaryFiniteContext.pack,
      BinaryCross.nodeBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,extractPrefix_pairBits,discardPrefix_pairBits]
    rw [show historyBits P++cons (labels H) []=historyBits (P++[H]) by rw [BinaryCoupled.historyBits_append,BinaryCoupled.historyBits_cons]; rfl]
    rw [BinaryCoupled.same_pack]
    rfl
  | sensitive H G T U=>
    have hv:=view_pack distance loc F (PhaseHistoryTransfer.after ∅ P) B v z lam n q key (20*N*M) k precision P H G T U
    change view (pack base n q key (20*N*M) k precision B P (.sensitive H G T U))=_ at hv
    simp only [run,rf,Function.comp_apply,pack,BinaryCross.resultBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,show (2:ℕ)≠0 by omega,show (2:ℕ)≠1 by omega,ite_false, if_false]
    change sensitive (pack base n q key (20*N*M) k precision B P (.sensitive H G T U))=_
    unfold sensitive
    rw [hv]
    cases he : CanonicalLengthView.view (rows distance) (F.image original) ((F.sort (·≤·)).map original) H G with
    | none=>
      simp only [Option.map_none,Find.optionEncode,ite_true, if_true]
      simp only [fallbackInput,bf,Function.comp_apply,pack,base,BinaryFiniteContext.pack,
        field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
      change pairBits ([],BinaryCoupled.finish (encode [setBits B,BinaryRational.encode lam,historyBits P,historyBits (m:=m) []]))=_
      rw [BinaryCoupled.finish_pack]
      simp only [CanonicalCoupledMerge.resolve,he]
      rfl
    | some J=>
      simp only [Option.map_some,Find.optionEncode,List.cons_ne_nil,ite_false, if_false]
      have hs : sensitiveInput (pack base n q key (20*N*M) k precision B P (.sensitive H G T U))=
          BinarySensitive.pack base n q key (20*N*M) k precision H T U J := by
        unfold sensitiveInput plan
        simp only [Function.comp_apply]
        rw [hv]
        simp only [he,Option.map_some,Find.optionEncode,List.tail_cons,BinaryResolve.H,BinaryResolve.T,BinaryResolve.U,rf,Function.comp_apply,
          pack,BinaryCross.resultBits,BinaryCross.nodeBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
          extractPrefix_pairBits,discardPrefix_pairBits,BinarySensitive.pack]
      unfold planResultInput
      rw [hs,BinarySensitive.run_pack_s238r]
      simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
      change BinaryPlanResult.run (BinaryPlanResult.pack (BinarySensitive.pack base n q key (20*N*M) k precision H T U J) B P
        (CanonicalSensitiveEndpoint.run loc distance F (PhaseHistoryTransfer.after ∅ P) v lam (20*N*M) q n k key precision H T U J))=_
      rw [BinaryPlanResult.run_pack]
      simp only [CanonicalCoupledMerge.resolve,he]
      generalize CanonicalSensitiveEndpoint.run loc distance F (PhaseHistoryTransfer.after ∅ P) v lam (20*N*M) q n k key precision H T U J=R
      cases R <;> rfl
end MetricKMedianRecovery.BitMachine.BinaryResolve

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryResolve.run_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryResolve.run_pack_s238r_oai
