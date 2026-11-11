-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_pack_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:55:07.536255+00:00
-- url     : https://prove2.me/submissions/073e6e46-e79a-482b-82f2-f8654a4a1cd8

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K022
import Definitions.Def_Q238K034
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCross_finalCount_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_countInter_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_union_list_pack_s238

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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace WordList
lemma lengthBits_encode (ws : List (List Bool)) : lengthBits (encode ws)=ws.length.bits := by
  simp only [lengthBits,Function.comp_apply,Count.run_encode,UnaryResources.lengthBits_eq,List.length_replicate]
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CrossCount
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

lemma opened_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (H : List (Label (Fin m))) (T : List (List (Label (Fin m)))) :
    opened (pairBits (ctxBits F Q k,nodeBits (H,T)))=setBits (Q∪H.toFinset) := by
  simp only [opened,cf,Function.comp_apply,ctxBits,nodeBits,field_encode,extractPrefix_pairBits,discardPrefix_pairBits,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFiniteContext.union_list_pack_s238]
lemma paid_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (H : List (Label (Fin m))) (T : List (List (Label (Fin m)))) :
    paid (pairBits (ctxBits F Q k,nodeBits (H,T)))=(CanonicalMergeCrossing.paid F Q H).bits := by
  rw [paid,opened_pack]
  simp only [cf,Function.comp_apply,ctxBits,field_encode,extractPrefix_pairBits,
    List.getElem?_cons_zero,Option.getD_some,BinaryFiniteContext.countInter_pack_s238,CanonicalMergeCrossing.paid]
end MetricKMedianRecovery.BitMachine.BinaryCross

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CrossEdge
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
attribute [local irreducible] paid finalCount

lemma forward_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (H G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) :
    forward (pack F Q k (H,T) (G,U))=CanonicalMergeCrossing.forward F Q H G := by
  simp only [forward,leftPaid,rightPaid,leftData,rightData,leftNode,rightNode,leftLength,rightLength,pack,
    Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [paid_pack,paid_pack]
  simp only [nodeBits,extractPrefix_pairBits,labels,lengthBits_encode,List.length_map,value_bits,
    decide_eq_true_eq,CanonicalMergeCrossing.forward]

lemma mixed_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (H G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) :
    mixed (pack F Q k (H,T) (G,U))=nodeBits (G,T) := by
  simp only [mixed,pack,leftNode,rightNode,Function.comp_apply,nodeBits,extractPrefix_pairBits,discardPrefix_pairBits]
lemma directed_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (H G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) :
    directed (pack F Q k (H,T) (G,U))=resultBits (CanonicalMergeCrossing.directed F Q k H G T U) := by
  simp only [directed,mixedCommon,mixedCount,mixed_pack]
  simp only [leftLength,rightLength,leftNode,rightNode,pack,Function.comp_apply,extractPrefix_pairBits,
    discardPrefix_pairBits]
  rw [finalCount_pack_s238]
  simp only [cf,Function.comp_apply,extractPrefix_pairBits,ctxBits,nodeBits,labels,lengthBits_encode,
    List.length_map,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    value_bits,decide_eq_true_eq]
  unfold CanonicalMergeCrossing.directed
  split_ifs <;> simp only [successNode,taggedPair,resultBits,nodeBits,labels,extractPrefix_pairBits,discardPrefix_pairBits]

lemma edge_pack_s238_oai {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (H G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) :
    edge (pack F Q k (H,T) (G,U))=resultBits (CanonicalMergeCrossing.edge F Q k H G T U) := by
  have hf : flipped (pack F Q k (H,T) (G,U))=pack F Q k (G,U) (H,T) := by
    simp only [flipped,pack,leftNode,rightNode,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [edge,forward_pack,hf]
  unfold CanonicalMergeCrossing.edge
  split_ifs <;> rw [directed_pack]
end MetricKMedianRecovery.BitMachine.BinaryCross

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_pack_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_pack_s238_oai
