-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.count_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:13:21.720466+00:00
-- url     : https://prove2.me/submissions/810099cc-6e9a-4cc7-bab8-910a5835b348

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L043
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_countInter_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_union_list_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryLengthQuery_chosen_pack_s238r

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
end Flatten
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_FiniteMachine
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
lemma labels_cons {m : ℕ} (x : Label (Fin m)) (xs : List (Label (Fin m))) :
    labels (x::xs)=WordList.cons (BinaryLabel.encode x) (labels xs) := rfl
lemma labels_nil {m : ℕ} : labels ([] : List (Label (Fin m)))=[] := rfl

end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteMachine
open WordOperations WordList RationalLeaves PhaseSequence
open BinaryFiniteContext (labels setBits)
lemma flatten_historyBits {m : ℕ} (hs : List (List (Label (Fin m)))) :
    Flatten.run (historyBits hs)=labels hs.flatten := by
  rw [historyBits,Flatten.run_encode]
  induction hs with
  | nil=>rfl
  | cons H hs ih=>simp only [List.map_cons,List.flatten_cons,ih,BinaryFiniteContext.labels_append]
lemma after_pack {m : ℕ} (Q : Finset (Label (Fin m))) (hs : List (List (Label (Fin m)))) :
    after (pairBits (setBits Q,historyBits hs))=setBits (PhaseHistoryTransfer.after Q hs) := by
  simp only [after,extractPrefix_pairBits,discardPrefix_pairBits,flatten_historyBits]
  have hh:=BinaryFiniteContext.union_list_pack_s238r Q hs.flatten
  simp only [BinaryFiniteContext.union,extractPrefix_pairBits,discardPrefix_pairBits] at hh
  rw [hh]
  congr 1
  clear hh
  induction hs generalizing Q with
  | nil=>simp only [List.flatten_nil,List.toFinset_nil,Finset.union_empty,PhaseHistoryTransfer.after]
  | cons H hs ih=>simpa only [List.flatten_cons,List.toFinset_append,←Finset.union_assoc,PhaseHistoryTransfer.after] using ih (Q∪H.toFinset)
end MetricKMedianRecovery.BitMachine.BinaryFiniteMachine

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
lemma count_pack_s238r_oai {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (i : Label (Fin m)) (b s : ℚ)
    (T U : List (List (Label (Fin m)))) :
    count (pairBits (ctxBits (BinaryFiniteContext.pack distance loc F Q v z lam) n q key i b T U,BinaryRational.encode s))=
      (CanonicalLengthSearch.count F Q (leaf key (parent i))
        (fun s=>FiniteLabelContinuation.continuation loc (rows distance) F v lam q n (insert (leaf key (parent i) s) Q)) T U b s).bits := by
  simp only [count,finalOpened,opened_pack,chosen_pack_s238r,BinaryFiniteMachine.after_pack]
  simp only [cf,Function.comp_apply,extractPrefix_pairBits,ctxBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,BinaryFiniteContext.pack,BinaryFiniteContext.countInter_pack_s238r,
    CanonicalLengthSearch.count]
end MetricKMedianRecovery.BitMachine.BinaryLengthQuery

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.count_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.count_pack_s238r_oai
